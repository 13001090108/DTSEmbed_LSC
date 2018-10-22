package softtest.rules.keilc.fault;

import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTConstant;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.VexNode;
import softtest.domain.c.analysis.ExpressionValueVisitor;
import softtest.domain.c.analysis.ExpressionVistorData;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.IntegerDomain;
import softtest.domain.c.interval.IntegerInterval;
import softtest.domain.c.symbolic.Expression;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.Variable;
import softtest.rules.c.BasicStateMachine;
import softtest.rules.c.StateMachineUtils;
import softtest.summary.c.MethodSummary;
import softtest.summary.keilc.fault.MethodOOBPreCondition;
import softtest.summary.keilc.fault.MethodOOBPreConditionVisitor;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.NameDeclaration;
import softtest.symboltable.c.Search;
import softtest.symboltable.c.SourceFileScope;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.Type.CType_BaseType;
/**
 * 带函数摘要的数组越界自动机
 * @author zys	
 * 2010-5-12
 */
public class OOBSUMMARYStateMachine extends BasicStateMachine{

	public static List<FSMMachineInstance> createOOBSUMMARYStateMachines(SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		/** 查找当前函数的所有函数调用节点，对存在MethodOOBPreCondition的函数进行OOB检测 */
		String xPath=".//PrimaryExpression[@Method='true']";
		List<SimpleNode> funcNodeList = StateMachineUtils.getEvaluationResults(node, xPath);
		for (SimpleNode funcNode : funcNodeList) 
		{
			MethodNameDeclaration mnd=((ASTPrimaryExpression)funcNode).getMethodDecl();
			MethodSummary ms=mnd.getMethodSummary();
			if(ms!=null)
			{
				MethodOOBPreCondition preCondition = (MethodOOBPreCondition)ms.findMethodFeature(MethodOOBPreCondition.class);
				if(preCondition!=null)
				{
					FSMMachineInstance fsmInstance = fsm.creatInstance();
					fsmInstance.setRelatedASTNode(funcNode);
					fsmInstance.setStateData(preCondition);
					list.add(fsmInstance);
				}
			}
		}
		return list;
	}
	
	public static boolean checkFunctionCallOOB(List<ASTPrimaryExpression> nodes, FSMMachineInstance fsmin)
	{
		//是否检测出错的标志位
		boolean b=false;
		for(ASTPrimaryExpression funcNode:nodes)
		{
			if (!fsmin.getRelatedASTNode().equals(funcNode)) 
			{
				continue;
			}
			
			MethodOOBPreCondition preCondition = (MethodOOBPreCondition) fsmin.getStateData();
			Set<Variable> subScriptVarSet = preCondition.getSubScriptVariableSet();
			
			for (Variable subScriptVar : subScriptVarSet) 
			{
				IntegerInterval summaryInterval = preCondition.getSubScriptInterval(subScriptVar);
				
				//获取函数前置结束所关联变量的区间
				Domain d=null;
				
				//根据形参的下标位置，得到实参处的下标变量,目前只处理单变量的情况如f(i) f(1),f(i+j)之类的暂时不处理
				if(funcNode.jjtGetParent().jjtGetNumChildren()==1||!subScriptVar.isParam())
				{//无参数的函数调用，如f(); 此种情况前置条件所关联的变量必然为全局变量    
				//补充：（chh）有参数的函数调用，前置条件所关联的变量也有可能是全局变量,所以加了变量是否是全局变量的判断
					NameDeclaration var=Search.searchInVariableUpward(subScriptVar.getName(), funcNode.getScope());
					if(var!=null)
					{
						d=getDomain(funcNode, (VariableNameDeclaration) var);
					}
				}else{
					ASTAssignmentExpression assignExpr=(ASTAssignmentExpression) funcNode.getNextSibling().jjtGetChild(subScriptVar.getParamIndex());
					ASTPrimaryExpression priExpr=(ASTPrimaryExpression) assignExpr.getSingleChildofType(ASTPrimaryExpression.class);
					if(priExpr!=null)
					{
						VariableNameDeclaration var=priExpr.getVariableNameDeclaration();
						if(var!=null)
						{
							//如果形参是变量，如f(i)
							d=getDomain(funcNode, var);
						}else{
							//如果形参是常数,，如f(1)
							ASTConstant cons=(ASTConstant) priExpr.getSingleChildofType(ASTConstant.class);
							int value=Integer.parseInt(cons.getImage());
							d=new IntegerDomain(new IntegerInterval(value,value));
						}
					}else{
						//如果实参既不是单个变量，也不是单个常数，则计算该实参表达式的值比如f(a+b)
						ExpressionValueVisitor expvst = new ExpressionValueVisitor();
						ExpressionVistorData visitdata = new ExpressionVistorData();
						visitdata.currentvex = assignExpr.getCurrentVexNode();
	
						visitdata.currentvex.setfsmCompute(true);
						expvst.visit(assignExpr, visitdata);
						visitdata.currentvex.setfsmCompute(false);
						
						Expression value1 = visitdata.value;
						d = value1.getDomain(visitdata.currentvex.getLastsymboldomainset());
					}
				}
				
				//modified by nmh
				if(d==null || Domain.isEmpty(d) || d.isUnknown())
					continue;
				//由于是数组下标的值域，所以只讨论整形区间
				Domain temp=Domain.intersect(new IntegerDomain(summaryInterval), d, CType_BaseType.intType);
				
				if(temp!=null && Domain.isEmpty(temp))
				{
					if(fsmin.getDesp()==null || fsmin.getDesp().length()==0)
					{
						String desp = "在代码第"+funcNode.getBeginLine()+"调用";
						fsmin.setDesp(desp+preCondition.getSubScriptDesp(subScriptVar));
					}else{
						String desp =fsmin.getDesp()+"\n";
						fsmin.setDesp(desp+preCondition.getSubScriptDesp(subScriptVar));
					}
					b=true;
				}
			}
		}
		return b;
	}
	
	private static Domain getDomain(SimpleNode funcNode, VariableNameDeclaration var)
	{
		Domain d=null;
		if(var==null)
			return d;
		
		VexNode vex=funcNode.getCurrentVexNode();
		d=vex.getVarDomainSet().getDomain(var);
		if(d==null && var.getScope() instanceof SourceFileScope)
		{//如果是全局变量，且其区间在控制流图上未知，则试图获取其初始化值：
			Object initValue=var.getVariable().getValue();
			if(initValue!=null){
				try{
					long t=((Long)initValue).longValue();
					d=new IntegerDomain(t,t);
				}catch(Exception e){
					d=null;
				}
			}
		}
		
		return d;
	}
	
	@Override
	public void registFetureVisitors() {
		super.registFetureVisitors();
		InterContext.addPreConditionVisitor(MethodOOBPreConditionVisitor.getInstance());
	}

}
