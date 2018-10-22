package softtest.rules.gcc.fault;

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTRelationalExpression;
import softtest.ast.c.ASTEqualityExpression;
import softtest.ast.c.ASTSelectionStatement;
import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.Edge;
import softtest.cfg.c.VexNode;
import softtest.domain.c.analysis.ExpressionValueVisitor;
import softtest.domain.c.analysis.ExpressionVistorData;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.DoubleDomain;
import softtest.domain.c.interval.IntegerDomain;
import softtest.domain.c.interval.IntegerInterval;
import softtest.domain.c.symbolic.Expression;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.Variable;
import softtest.rules.c.BasicStateMachine;
import softtest.rules.c.StateMachineUtils;
import softtest.summary.c.MethodFeature;
import softtest.summary.c.MethodSummary;
import softtest.summary.gcc.fault.MethodOOBPreCondition;
import softtest.summary.gcc.fault.MethodOOBPreConditionVisitor;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.NameOccurrence;
import softtest.symboltable.c.Scope;
import softtest.symboltable.c.SourceFileScope;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.NameOccurrence.OccurrenceType;
import softtest.symboltable.c.Type.CType_Array;


/**
 * @author chh  
 */
public class OOB_CheckStateMachine extends BasicStateMachine 
{
	private static Set<String> visitNode ;
	@Override
	public void registFetureVisitors() {
		super.registFetureVisitors();
		InterContext.addPreConditionVisitor(MethodOOBPreConditionVisitor.getInstance());
	}

    public static List<FSMMachineInstance> createOOBStateMachines(SimpleNode node, FSMMachine fsm) {
    	List<FSMMachineInstance> list = null;
    	String xpath = ".//UnaryExpression/PostfixExpression[@Operators='['][/Expression/AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression]/PrimaryExpression" +
    			"|.//PostfixExpression[/ArgumentExpressionList/AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression]/PrimaryExpression[@Method='true']";
        List<SimpleNode> results = StateMachineUtils.getEvaluationResults(node, xpath);
        for(SimpleNode snode : results) {
        	VariableNameDeclaration varDecl = snode.getVariableNameDeclaration();
        	if(varDecl==null){
        		 MethodNameDeclaration methodDecl = StateMachineUtils.getMethodNameDeclaration(snode);
                 if(methodDecl == null) {
                     continue;
                 }
                 MethodSummary mtSummary = methodDecl.getMethodSummary();
                 if(mtSummary == null) {
                     continue;
                 }
                 xpath ="/ArgumentExpressionList/AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression"   ;
                 List<SimpleNode> result = StateMachineUtils.getEvaluationResults((SimpleNode) snode.jjtGetParent(), xpath);
                 ASTPrimaryExpression priNode = (ASTPrimaryExpression)result.get(0);
                 VariableNameDeclaration var = priNode.getVariableNameDeclaration();
                 if(var==null)
                	 continue;
                 if(!(var.isParam()||var.getScope() instanceof SourceFileScope))
                 	continue;
                 MethodOOBPreCondition pre = (MethodOOBPreCondition) mtSummary.findMethodFeature(MethodOOBPreCondition.class);//(MethodOOBPreCondition) feature;
                 Set<Variable> subScriptVarSet =null;
                 if(pre!=null){
                	 subScriptVarSet = pre.getSubScriptVariableSet();
                	  for(Variable npdVar : subScriptVarSet) {
                          if(var.getVariable()!=null&&var.getVariable().equals(npdVar)) {
                         /*
                          * 取变量的限制条件和描述
                          */
                          IntegerInterval summaryInterval = pre.getSubScriptInterval(npdVar);
                          String desp = "在代码第"+priNode.getBeginLine()+"调用"+pre.getSubScriptDesp(npdVar);
                          Object[] res = ableToCheck(priNode,var);  
                          if(res[0].toString()=="true" && res[1] != null){//判断是否可check
                          	  if( checkOOB((ASTPrimaryExpression)res[1],summaryInterval,var)){//判断是否OOB
                          		  list=addFSM(snode,null,fsm,desp+"(在"+((ASTPrimaryExpression)res[1]).getBeginLine()+"行对下标变量进行了条件判断)");
                          	  }
                          	  
                             }
                          }
                      }
                 }
                         
                 
        	}
        	else{
        		if(varDecl.isParam()||varDecl.getScope() instanceof SourceFileScope)
                	continue;
                
                if(varDecl.getType().isArrayType()) {
                        xpath ="/Expression/AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression"   ;
                        List<SimpleNode> result = StateMachineUtils.getEvaluationResults((SimpleNode) snode.jjtGetParent(), xpath);
                        ASTPrimaryExpression priNode = (ASTPrimaryExpression)result.get(0);
                        VariableNameDeclaration var = priNode.getVariableNameDeclaration();
                        if(var==null||!(var.isParam()||var.getScope() instanceof SourceFileScope))
                        	continue;
                        /*
                         * 取数组大小和设置故障描述
                         */
                        Long length = ((CType_Array)varDecl.getType().getSimpleType()).getDimSize();
                        //防止由于区间错误导致大小为-1或0 的数组的误报
                        IntegerInterval size=new IntegerInterval(0,length!=0&&length!=-1?length-1:0);
                        String desp = "在第 " + varDecl.getNode().getBeginLine() + " 行定义的大小为 " + size+ " 的数组或指针\""+varDecl.getImage()+"\"可能在第"+snode.getBeginLine()+"行越界 ";
                        Object[] res = ableToCheck(priNode,var);
                        if(res[0].toString()=="true" && res[1] != null && size.getMax()!=0){//判断是否可check
                        	if(checkOOB((ASTPrimaryExpression)res[1],size,var)){//判断是否OOB
                        		list=addFSM(snode,varDecl,fsm,desp+"(在"+((ASTPrimaryExpression)res[1]).getBeginLine()+"行对下标变量进行了条件判断)");
                        	}
                        }
                	}
                else continue;
        	}
        }
        return list;
    }
    public static Object[] ableToCheck(ASTPrimaryExpression priNode,VariableNameDeclaration var){
    	Object[] res = new Object[2];
    	Scope scope = var.getScope();
		Map<VariableNameDeclaration, ArrayList<NameOccurrence>> varOccs = scope.getVariableDeclarations();
    	List<NameOccurrence> occs = varOccs.get(var);
    	boolean flag = false,result = false;
    	ASTPrimaryExpression resultNode=null;
    	int count = 0;
     	while(count <2){
     		if(count==1)
     			occs = reverse(occs);
        out:	for(NameOccurrence occ: occs){
         		if(occ.getLocation()==priNode){
        			flag = true;
        			continue;
        		}
        		if(flag){
        			if(occ.getOccurrenceType() == OccurrenceType.DEF||
        					occ.getOccurrenceType() == OccurrenceType.DEF_AFTER_USE){
        				flag = false;
        				result = false;
        				break;
        			}
        			else if(occs.get(occs.indexOf(occ)).getOccurrenceType() == OccurrenceType.USE){
        				if(occ.getLocation().getCurrentVexNode()!=null && occ.getLocation().getCurrentVexNode().getName().startsWith("if_head")
        						&&!(priNode.getParentsOfType(ASTSelectionStatement.class).contains(occ.getLocation().getFirstParentOfType(ASTSelectionStatement.class)))){
        					SimpleNode occNode = occ.getLocation();
        					if(priNode.getCurrentVexNode() !=null){
        						VexNode[] pre = new VexNode[2];
        						VexNode  tail ;
        						int i=0;
        						if(count == 0){
        							pre[0] = priNode.getCurrentVexNode();
        							tail = occNode.getCurrentVexNode();
        						}
        						else{
        							Hashtable<String,Edge>  preEdges = occNode.getCurrentVexNode().getOutedges();
        							for(String str : preEdges.keySet()){
        							   if(i>1)
         								   continue out;
     								   Edge e = preEdges.get(str);
     								   pre[i] = e.getHeadNode();
     								   i++;
     							   	}  
        							i--;
        							tail = priNode.getCurrentVexNode();
        						}
        						for(; i >= 0; i--){
        							visitNode = new TreeSet<String>();
            						if(!haveRoad(pre[i] , tail))
            							continue out;
        						}
        					}
        					else {
        						count = 1;
        						break;
        					}
        					if(occNode.getFirstParentOfType(ASTUnaryExpression.class).jjtGetParent() instanceof ASTEqualityExpression
        							&&occNode.getFirstParentOfType(ASTUnaryExpression.class).jjtGetParent().jjtGetNumChildren()==2){
        						result = true;
        						if(occNode.getIndexOfParent() == 1)
        							resultNode = (ASTPrimaryExpression) ((SimpleNode)occNode.getFirstParentOfType(ASTUnaryExpression.class).jjtGetParent().jjtGetChild(0)).getSingleChildofType(ASTPrimaryExpression.class);
        						else 
        							resultNode = (ASTPrimaryExpression) ((SimpleNode)occNode.getFirstParentOfType(ASTUnaryExpression.class).jjtGetParent().jjtGetChild(1)).getSingleChildofType(ASTPrimaryExpression.class);
        						break;
        					}
        					else if(occNode.getFirstParentOfType(ASTUnaryExpression.class).jjtGetParent() instanceof ASTRelationalExpression){
        						result = true;
        						if(occNode.getIndexOfParent() == 1)
        							resultNode = (ASTPrimaryExpression) ((SimpleNode)occNode.getFirstParentOfType(ASTUnaryExpression.class).jjtGetParent().jjtGetChild(0)).getSingleChildofType(ASTPrimaryExpression.class);
        						else 
        							resultNode = (ASTPrimaryExpression) ((SimpleNode)occNode.getFirstParentOfType(ASTUnaryExpression.class).jjtGetParent().jjtGetChild(1)).getSingleChildofType(ASTPrimaryExpression.class);
        						break;
        					}
        					else continue;
        				}
        				else continue;
        			}
        		}
        	}
        	if(result == true)
        		break;
        	else 
        		count++;
     	}

    	
    	res[0] = result;
    	res[1] = resultNode;
    	return res;
    }
    public static boolean checkOOB(ASTPrimaryExpression priNode,IntegerInterval size,VariableNameDeclaration var){
    	long max = Long.MAX_VALUE,min = Long.MIN_VALUE;
    	ExpressionValueVisitor expvst = new ExpressionValueVisitor();
		ExpressionVistorData visitdata = new ExpressionVistorData();
		visitdata.currentvex = priNode.getCurrentVexNode();
		visitdata.currentvex.setfsmCompute(true);
		expvst.visit(priNode, visitdata);
		visitdata.currentvex.setfsmCompute(false);
		Expression value1 = visitdata.value;
		Domain d=null;
		if(value1!=null)
		d = value1.getDomain(visitdata.currentvex.getLastsymboldomainset());
		if(d == null || !d.isNumberDomain())
			return false;
		if(d instanceof DoubleDomain)
			return false;
		if(((IntegerDomain) d).getMax()!=Long.MAX_VALUE&&((IntegerDomain) d).getMax()!=Long.MIN_VALUE){
			max = ((IntegerDomain) d).getMax();
			min = ((IntegerDomain) d).getMax();	
		}
		
    	if(priNode.getFirstParentOfType(ASTUnaryExpression.class).jjtGetParent() instanceof ASTRelationalExpression){
    		if(((SimpleNode)priNode.getFirstParentOfType(ASTUnaryExpression.class).jjtGetParent()).getOperators().startsWith(">")){
    			if(max!= Long.MAX_VALUE&&size.getMax()!=Long.MAX_VALUE&&max>size.getMax()) 
    				return true;
    		}
    		else{
    			if(min!= Long.MIN_VALUE&&size.getMin()!=Long.MIN_VALUE&&min<size.getMin())
    				return true;
    		}
    	}
    	else if(priNode.getFirstParentOfType(ASTUnaryExpression.class).jjtGetParent() instanceof ASTEqualityExpression){
    		if((max>size.getMax()||min<size.getMin())&&max!= Long.MAX_VALUE&&size.getMax()!=Long.MAX_VALUE&&size.getMin()!=Long.MIN_VALUE){
    			return true;
    		}
    	}
    	return false;
    }
   
    
    private static List<FSMMachineInstance> addFSM(SimpleNode node, VariableNameDeclaration var, FSMMachine fsm, String desp) {
        List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
        FSMMachineInstance instance = fsm.creatInstance();
        instance.setRelatedASTNode(node);
        instance.setRelatedVariable(var);
        instance.setDesp(desp);
        list.add(instance);
        return list;
    }
   private static List<NameOccurrence> reverse(List<NameOccurrence> list){
	   List<NameOccurrence> reverseList = new LinkedList<NameOccurrence>() ;
	   for(int i=0;i<list.size();i++){
		   reverseList.add(list.get(list.size()-1-i));
	   }
	   return reverseList;
   }
   
   public static boolean haveRoad(VexNode pre, VexNode tail){
	   boolean flag = false;
	   Hashtable<String,Edge>  preEdges = pre.getOutedges();
	   visitNode.add(pre.getName());
	   for(Edge e : preEdges.values()){
		   VexNode vNode = e.getHeadNode();
		   if(vNode.equals(tail)){
			   visitNode.add(vNode.getName());
			   flag = true;
			   break;
		   }
		   else if(!visitNode.add(vNode.getName())){
			   continue;
		   }
		   else if(vNode.getName().startsWith("func_out")){
			   visitNode.add(vNode.getName());
			   continue;
		   }
		   else{
			   flag = haveRoad(vNode, tail);
			   if(flag)
				   break;
		   }
	   }
	   return flag;
   }
}
