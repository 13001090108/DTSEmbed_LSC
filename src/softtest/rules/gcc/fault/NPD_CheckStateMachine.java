package softtest.rules.gcc.fault;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTEqualityExpression;
import softtest.ast.c.ASTExpression;
import softtest.ast.c.ASTIterationStatement;
import softtest.ast.c.ASTPostfixExpression;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTSelectionStatement;
import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.VexNode;
import softtest.domain.c.analysis.ConditionData;
import softtest.domain.c.analysis.ExpressionValueVisitor;
import softtest.domain.c.analysis.ExpressionVistorData;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.DomainType;
import softtest.domain.c.interval.IntegerDomain;
import softtest.domain.c.interval.IntegerInterval;
import softtest.domain.c.interval.PointerDomain;
import softtest.domain.c.interval.PointerValue;
import softtest.domain.c.symbolic.Expression;
import softtest.domain.c.symbolic.SymbolFactor;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.Variable;
import softtest.rules.c.BasicStateMachine;
import softtest.rules.c.StateMachineUtils;
import softtest.summary.c.MethodFeature;
import softtest.summary.c.MethodSummary;
import softtest.summary.gcc.fault.MethodNPDPreCondition;
import softtest.summary.gcc.fault.MethodNPDPreConditionVisitor;
import softtest.symboltable.c.LocalScope;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.NameDeclaration;
import softtest.symboltable.c.Scope;
import softtest.symboltable.c.Search;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.Type.CType;
import softtest.symboltable.c.Type.CType_Array;
import softtest.symboltable.c.Type.CType_Function;
import softtest.symboltable.c.Type.CType_Pointer;

public class NPD_CheckStateMachine extends BasicStateMachine {

    @Override
    public void registFetureVisitors() {
        super.registFetureVisitors();
        InterContext.addPreConditionVisitor(MethodNPDPreConditionVisitor.getInstance());
    }

    static class Info {
    	VariableNameDeclaration var;
    	SimpleNode node; //if对应的顶点
    }
    public static List<FSMMachineInstance> createNPD_CheckStateMachines(SimpleNode node, FSMMachine fsm) {
        List<FSMMachineInstance> list = null;
        if(!node.getFileName().contains(".h"))
        { 
        	Set<VariableNameDeclaration> vars = collectVariables(node);
        // 检查每一个变量是否满足NPD_PRE_Check的条件
        for(VariableNameDeclaration var : vars) {
        	Info info = new Info();
        	info.var = var;
            if(isNPDPreCheck(node, info)) {
                Object[] res = checkDereference(node, info);
                if(res != null) {
                    list = addFSM((SimpleNode)res[0], var, fsm, (String)res[1]);
                    continue;
                }
                res = checkUseInFunction(node, info);
                if(res != null) {
                    list = addFSM((SimpleNode)res[0], var, fsm, (String)res[1]);
                    continue;
                }
            }
        	}
        }
        return list;
    }
    
    /**
     * 收集全局、类成员、参数中出现的指针变量   收集所有在node函数节点中使用的变量
     */
    private static Set<VariableNameDeclaration> collectVariables(SimpleNode node) {
        Set<VariableNameDeclaration> vars = new HashSet<VariableNameDeclaration>();
        Scope scope = node.getScope();
        if(scope != null) {
            for(Object key : scope.getVariableDeclarations().keySet()) {
            	VariableNameDeclaration var = (VariableNameDeclaration) key;
                if(var.getType() instanceof CType_Pointer) {
                	  vars.add(var);
                }
            }
            //增加对全局变量的处理
           Scope sourceFileScope =  scope.getParent();
           if(sourceFileScope!=null)
           {
	           	Set<VariableNameDeclaration> keySet1 = sourceFileScope.getVariableDeclarations().keySet();
	           	for(Object key1: keySet1)
	        	{
	        		VariableNameDeclaration globalVar = (VariableNameDeclaration) key1;
	                if(globalVar.getType() instanceof CType_Pointer) {
	                    String varName = globalVar.getImage();
	                    String xpath=".//UnaryExpression/PostfixExpression/PrimaryExpression[@Image='" + varName + "']";
	                    List<SimpleNode> results = StateMachineUtils.getEvaluationResults(node, xpath);
	                    if(!results.isEmpty())
	                	  vars.add(globalVar);
	                }
	        	}
           }
            
            //增加对局部变量的处理 lrt
            List<Scope> list = scope.getChildrens();
            Iterator<Scope> iter=list.iterator();
            while(iter.hasNext())
            {
            	Scope s = iter.next();
            	Set<VariableNameDeclaration> keySet = s.getVariableDeclarations().keySet();
            	for(Object key: keySet)
            	{
            		VariableNameDeclaration localVar = (VariableNameDeclaration) key;
                    if(localVar.getType() instanceof CType_Pointer) {
                        vars.add(localVar);
                    }
            	}
            	
            }
            
        }
        return vars;
    }
    /**
     * 检查变量是否满足NDP_Pre_Check的条件 
     */
    private static boolean isNPDPreCheck(SimpleNode node, Info info) {
        String xpath = ".//UnaryExpression/PostfixExpression[count(*)=1]/PrimaryExpression[@Method='false' and @Image='" + info.var.getImage() + "'] " +
        		"       | .//UnaryExpression/PostfixExpression[@Method='false' and @Image='" + info.var.getImage() + "' ]";
        List<SimpleNode> results = StateMachineUtils.getEvaluationResults(node, xpath);
        for(SimpleNode snode : results) {
            VexNode vexnode = snode.getCurrentVexNode();
             List nodes;
            if(vexnode != null && vexnode.getName().startsWith("if_head"))
               nodes = snode.getParentsOfType(ASTSelectionStatement.class);
            else if(vexnode != null && vexnode.getName().startsWith("while_head"))////增加通过while判断是否为空
            	nodes = snode.getParentsOfType(ASTIterationStatement.class);
//            else if(vexnode!=null && vexnode.getName().startsWith("for_head"))
//            	nodes = snode.getParentsOfType(ASTIterationStatement.class);
//           
            else 
            	continue;
            SimpleNode n = null;
            if(!nodes.isEmpty()) {
                n = (SimpleNode) nodes.get(0);
            }
       
            if (n == null) {
            	continue;
            }
                info.node = n;
                List equality = snode.getParentsOfType(ASTEqualityExpression.class);
                if(equality.size() != 0) {      // if(p != 0)
                	ASTEqualityExpression equalityExp = (ASTEqualityExpression) equality.get(0);
                    if(equalityExp.jjtGetNumChildren() == 2 && (equalityExp.getOperators().equals("!=") || equalityExp.getOperators().equals("=="))) {
                        SimpleNode child1 = (SimpleNode) equalityExp.jjtGetChild(0);
                        SimpleNode child2 = (SimpleNode) equalityExp.jjtGetChild(1);
                        boolean isError = false;
                        if(//(child1.getImage().equals("0") || child2.getImage().equals("0"))
                                /*&&*/ (child1.getImage().equals(info.var.getImage()) || child2.getImage().equals(info.var.getImage()))) {
                            //if(child1.findChildrenOfType(ASTPrimaryExpression.class).size() == 1 && child2.findChildrenOfType(ASTPrimaryExpression.class).size() == 1) {

                          //  }
                        }
                        if(child1.getImage().equals(info.var.getImage()))
                		{
                        	// 获取指针变量
                			ExpressionValueVisitor exp = new ExpressionValueVisitor();
							ExpressionVistorData domaindata = new ExpressionVistorData();
							domaindata.currentvex = child2.getCurrentVexNode();
							exp.visit(child2, domaindata);

							Expression value1 = domaindata.value;
							Domain mydomain = null;
							if (value1 != null)
								mydomain = value1.getDomain(domaindata.currentvex.getSymDomainset());
							if (mydomain instanceof PointerDomain) {
								PointerDomain pd = (PointerDomain) mydomain;
								if (pd.getValue() == PointerValue.NULL) {
									isError = true;
								}
							}
							if (mydomain instanceof IntegerDomain) {
								IntegerDomain id = (IntegerDomain) mydomain;
								if (id.getMin() == 0 && id.getMax() ==0) {
									isError = true;
								}
							}
                		}
                        if(child2.getImage().equals(info.var.getImage()))
                		{
                        	// 获取指针变量
                			ExpressionValueVisitor exp = new ExpressionValueVisitor();
							ExpressionVistorData domaindata = new ExpressionVistorData();
							domaindata.currentvex = child1.getCurrentVexNode();
							exp.visit(child1, domaindata);

							Expression value1 = domaindata.value;
							Domain mydomain = null;
							if (value1 != null)
								mydomain = value1.getDomain(domaindata.currentvex.getSymDomainset());
							if (mydomain instanceof PointerDomain) {
								PointerDomain pd = (PointerDomain) mydomain;
								if (pd.getValue() == PointerValue.NULL) {
									isError = true;
								}
							}
							if (mydomain instanceof IntegerDomain) {
								IntegerDomain id = (IntegerDomain) mydomain;
								if (id.getMin() == 0 && id.getMax() ==0) {
									isError = true;
								}
							}
                		}
                        if(isError) {
                        	return true;
                        	//如果判断是否为空后  eg，if(x==null) {这里有return} 则不报错
//                            String path = ".//JumpStatement|.//PrimaryExpression[@Image='exit' and @Method='true']";
//                            List<SimpleNode> re = StateMachineUtils.getEvaluationResults(n, path);
//                            if(re== null || re.isEmpty()) {
//                                return true;
//                            }
                        }
                    }
                } else {
                	String xpath1=".//UnaryExpression[./UnaryOperator[@Operators='!']]/UnaryExpression/PostfixExpression[count(*)=1]/PrimaryExpression[@Method='false' and @Image='" + info.var.getImage() + "']";
                	List<SimpleNode> re = StateMachineUtils.getEvaluationResults(n, xpath1);
                	if(re!=null && !re.isEmpty())
                		return true;
                	// if(p)
                    ConditionData condition = vexnode.getCondata();
                    if(condition != null) {
                    	Expression ve=vexnode.getValue(info.var);
                    	if (ve == null || ve.getSingleFactor() == null) {
                    		continue;
                    	}
                        Domain may = condition.getMayDomain((SymbolFactor) ve.getSingleFactor());
                        Domain must = condition.getMustDomain((SymbolFactor) ve.getSingleFactor());
                        if(may != null && must != null && may instanceof PointerDomain) {
                                        String path = ".//JumpStatement|.//PrimaryExpression[@Name='exit' and @Method='true']";
                                        if(StateMachineUtils.getEvaluationResults(n, path).isEmpty()) {
                                            return true;
                                        }
                        }
                    }
                }
                 //处理最简单的通过 if(p) 或者 while(p)检查的情况
               
                	String xpath2=".//SelectionStatement/Expression[@DescendantDepth='4']//PrimaryExpression[@Method='false' and @Image=@Image='" + info.var.getImage() + "'] | .//IterationStatement/Expression[@DescendantDepth='4']//PrimaryExpression[@Method='false' and @Image=@Image='" + info.var.getImage() + "']";
                	List<SimpleNode> re = StateMachineUtils.getEvaluationResults(n, xpath2);
                	if(re!=null && !re.isEmpty())
                		return true;
         }
               
        String xpath1=".//ConditionalExpression";
        List<SimpleNode> results1 = StateMachineUtils.getEvaluationResults(node, xpath1);
        for(SimpleNode snode : results1) {
        	if(snode.jjtGetNumChildren() != 3)
        		continue;
        	SimpleNode child0 = (SimpleNode) snode.jjtGetChild(0);
        	if(child0.getImage().equals(info.var.getImage()))
        	   return true;
        }
        return false;
    }
    
    private static Object[] checkDereference(SimpleNode node, Info info) {
        // 指针变量的解引用出现 *a, a[x], a->x;
        String xpath = ".//AssignmentExpression//UnaryExpression/PostfixExpression[starts-with(@Operators,'[') or starts-with(@Operators,'->')]/PrimaryExpression[@Image='"+ info.var.getImage() +"']|" +
                ".//AssignmentExpression//UnaryExpression/PostfixExpression/PrimaryExpression[../../../UnaryOperator[@Operators='*'] and @Image='" + info.var.getImage() + "']" ;
        List<SimpleNode> results = StateMachineUtils.getEvaluationResults(node, xpath);
        for(SimpleNode snode : results) {
        	if (info.node != null && snode.getBeginLine() >= info.node.getBeginLine()  ) {
        		continue;
        	}
        	
            VariableNameDeclaration varDecl = snode.getVariableNameDeclaration();
            if(varDecl == info.var) {
            	//如果在引用点指针已经不为空 则返回 lrt
    			Domain pDomain =varDecl.getDomain();
    			if (pDomain != null && !pDomain.isUnknown() && pDomain instanceof PointerDomain && pDomain.getDomaintype() != DomainType.UNKNOWN) {
    				continue;
    			}

               List selections = snode.getParentsOfType(ASTSelectionStatement.class);
                if(selections.size() != 0) {
                    continue;
                }
                Object[] res = new Object[2];
                res[0] = snode;
                res[1] = "";
                return res;
            }
        }
      
        //判断多级指针是否被解引用 added by lrt
        String xpath1 = ".//AssignmentExpression//UnaryExpression/PostfixExpression[starts-with(@Image,'" + info.var.getImage() + "')][./PrimaryExpression]";
        List<SimpleNode> results1 = StateMachineUtils.getEvaluationResults(node, xpath1);
        for(SimpleNode sn : results1) {
        	if (info.node != null && sn.getBeginLine() >= info.node.getBeginLine() ) {
        		continue;
        	}
                ASTPostfixExpression postnode = (ASTPostfixExpression)sn;
    			ASTPrimaryExpression primExp = (ASTPrimaryExpression)postnode.getFirstChildOfType(ASTPrimaryExpression.class);
    			String StrExp = null;
    			if(!primExp.isMethod())
    			{
    				if( !(postnode.getImage().contains(".") || postnode.getImage().contains("->") ||postnode.getImage().contains("[")) || postnode.jjtGetNumChildren() < 3)
    				{
    					continue;
    				}
    				
    				//处理多级指针   由-> 和 [ 简单解引用 lrt
    				ArrayList<Boolean> flags=postnode.getFlags();
    				ArrayList<String> operators=postnode.getOperatorType();
    				
    				Scope localScope = postnode.getScope();
    				int operatorIndex=0;
    				boolean arrayFlag=true;
    				for(int i=0;i<flags.size();i++){
    					boolean flag=flags.get(i);
    					String operator=operators.get(flags.size()-i-1);
    					if(operator.equals("[")){
    						String image=postnode.getImage();
    						operatorIndex=image.indexOf("[", operatorIndex);
    						if(operatorIndex>0)
    						{							
    							image=image.substring(0, operatorIndex);
    							operatorIndex++;
    							NameDeclaration decl=Search.searchInVariableAndMethodUpward(image, localScope);
    				        								
    							if(decl!=null && (decl.getType() instanceof CType_Array||decl.getType() instanceof CType_Pointer)){
    				        		VariableNameDeclaration v=(VariableNameDeclaration)decl;			        		
    				        		if(v==info.var)
    				        		{
    				        			  
    				        			//如果在引用点指针已经不为空 则返回 lrt
    				        			Domain pDomain =v.getDomain();
    				        			if (pDomain != null && !pDomain.isUnknown() && pDomain instanceof PointerDomain && pDomain.getDomaintype() != DomainType.UNKNOWN) {
    				        				continue;
    				        			}

    				        			  Object[] res1 = new Object[2];
    				                       res1[0] = sn;
    				                       res1[1] = "";
    				                       return res1;
    				        		}
    				        	}	
    						}
    						else
    						{
    							
    							if(arrayFlag&&postnode.jjtGetChild(1)!=null &&postnode.jjtGetChild(1) instanceof ASTExpression)
    							{
    								
    								ASTExpression expressionNode=(ASTExpression)postnode.getFirstDirectChildOfType(ASTExpression.class);
    								if(expressionNode!=null)
    								{
    									ExpressionVistorData exprdata = new ExpressionVistorData();
    									exprdata.currentvex=expressionNode.getCurrentVexNode();
    									exprdata.sideeffect=true;
    									
    									ExpressionValueVisitor eVisitor=new ExpressionValueVisitor();
    									exprdata=(ExpressionVistorData)eVisitor.visit((ASTAssignmentExpression)expressionNode.getFirstDirectChildOfType(ASTAssignmentExpression.class), exprdata);									
    									Domain domain=exprdata.value.getDomain(exprdata.currentvex.getSymDomainset());
    									IntegerDomain vDomain=Domain.castToIntegerDomain(domain);
    									if(vDomain!=null)
    									{
    										
    										List<Integer> intNums=vDomain.getNums();
    										for(int intN=0;intN<intNums.size();intN++)
    										{
    											int index=intNums.get(intN).intValue();
    											String arrImage=primExp.getImage()+"["+index+"]";
    											NameDeclaration declArrar=Search.searchInVariableAndMethodUpward(arrImage, localScope);
    											
    											if(declArrar!=null&&declArrar.getType() instanceof CType_Pointer)
    											{
    												VariableNameDeclaration vArray=(VariableNameDeclaration)declArrar;
    												if(vArray==info.var)
    			    				        		{
    													//如果在引用点指针已经不为空 则返回 lrt
    									    			Domain pDomain =vArray.getDomain();
    									    			if (pDomain != null && !pDomain.isUnknown() && pDomain instanceof PointerDomain && pDomain.getDomaintype() != DomainType.UNKNOWN) {
    									    				continue;
    									    			}

    													
    													   Object[] res1 = new Object[2];
    			    				                       res1[0] = sn;
    			    				                       res1[1] = "";
    			    				                       return res1;
    			    				        		}
    											
    											}else
    											{
    												break;
    											}
    											
    										}
    									}
    								}
    							}
    						}
    					}else 
    					if(operator.equals("->")){
    						String image=postnode.getImage();
    						operatorIndex=image.indexOf("->", operatorIndex);
    						if(operatorIndex>0)
    						{
    							image=image.substring(0, operatorIndex);
    							operatorIndex+=2;
    							NameDeclaration decl=Search.searchInVariableAndMethodUpward(image, localScope);
    				        	if(decl!=null && decl.getType() instanceof CType_Pointer){
    				        		VariableNameDeclaration v=(VariableNameDeclaration)decl;
    				        		if(v==info.var)
    				        		{
    				        			
    				        			Domain pDomain =v.getDomain();
    				        			if (pDomain != null && !pDomain.isUnknown() && pDomain instanceof PointerDomain && pDomain.getDomaintype() != DomainType.UNKNOWN)
    				        				continue;
    				        			   Object[] res1 = new Object[2];
    				                       res1[0] = sn;
    				                       res1[1] = "";
    				                       return res1;
    				        		}
    				        	}
    						}
    					}									
    				}
    				
    			   }		
        }			
	    return null;
    }
    
    private static Object[] checkUseInFunction(SimpleNode node, Info info) {
        String xpath = ".//PostfixExpression[.//UnaryExpression/PostfixExpression/PrimaryExpression[@Image='" + info.var.getImage() +"']]/PrimaryExpression[@Method='true']";
        List<SimpleNode> results = StateMachineUtils.getEvaluationResults(node, xpath);
        for(SimpleNode snode : results) {
        	if (info.node != null && snode.getBeginLine() >= info.node.getBeginLine() ) {
        		continue;
        	}
            MethodNameDeclaration methodDecl = StateMachineUtils.getMethodNameDeclaration(snode);
            if(methodDecl == null) {
                continue;
            }
            MethodSummary mtSummary = methodDecl.getMethodSummary();
            if(mtSummary == null) {
                continue;
            }
            for(MethodFeature feature : mtSummary.getPreConditions()) {
                if(feature instanceof MethodNPDPreCondition) {
                    MethodNPDPreCondition pre = (MethodNPDPreCondition) feature;
                    Variable variable = Variable.getVariable(info.var);
                    for(Variable npdVar : pre.getNPDVariables()) {
                    	 if (variable!= null && variable.getParamIndex() == npdVar.getParamIndex()) {
//                    		 List selections = snode.getParentsOfType(ASTSelectionStatement.class);
//                             if(selections.size() != 0) {
//                                 continue;
//                             }
                            Object[] res = new Object[2];
                            res[0] = snode;
                            res[1] = pre.getDespString(npdVar);
                            return res;
                        }
                    }
                }
            }
        }
        return null;
    }
    
    private static List<FSMMachineInstance> addFSM(SimpleNode node, VariableNameDeclaration var, FSMMachine fsm, String desp) {
        List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
        FSMMachineInstance instance = fsm.creatInstance();
        instance.setRelatedASTNode(node);
        instance.setRelatedVariable(var);
        instance.setDesp("变量" + var.getImage() + "在第" + node.getBeginLine() + "行可能为空指针引用" + desp);
        list.add(instance);
        return list;
    }
    
}
