package softtest.rules.gcc.fault;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.VexNode;
import softtest.config.c.Config;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.PointerDomain;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.Variable;
import softtest.rules.c.BasicStateMachine;
import softtest.rules.c.StateMachineUtils;
import softtest.summary.gcc.fault.MethodMMPreCondition;
import softtest.summary.gcc.fault.MethodMMPreConditionVisitor;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.Scope;
import softtest.symboltable.c.Search;
import softtest.symboltable.c.SourceFileScope;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.Type.CType_AllocType;

public class MLFPreGLobleVarStateMachine extends BasicStateMachine
{
	public void registFetureVisitors()
	{
		super.registFetureVisitors();
		InterContext.addSideEffectVisitor(MethodMMPreConditionVisitor
				.getInstance());
	}
	
	public static List<FSMMachineInstance> createMLFStateMachines(SimpleNode node, FSMMachine fsm)
	{
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		
		/*String xpath=".//Declaration/InitDeclaratorList/InitDeclarator/Initializer/AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression[@Method='true']"+
		"|.//Expression/AssignmentExpression/AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression[@Method='true']";*/
		String xpath = ".//UnaryExpression/PostfixExpression/PrimaryExpression[@Method='true']";
		
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		for(SimpleNode snode : evaluationResults)
		{
			ASTPrimaryExpression pExp = (ASTPrimaryExpression)snode;
			MethodNameDeclaration methodDecl = pExp.getMethodDecl();
			if(methodDecl != null && methodDecl.getMethodSummary() != null)
			{
				MethodMMPreCondition preFeature = (MethodMMPreCondition) methodDecl.getMethodSummary().findMethodFeature(MethodMMPreCondition.class);
				if(preFeature != null)
				{
					SourceFileScope sfScope = findSourceFileScope(snode.getScope());
					Set<Variable> vars = preFeature.getVariables();
					for(Variable var: vars)
					{
						VariableNameDeclaration varDecl = (VariableNameDeclaration)Search.searchInVariableAndMethodUpward(var.getName(), sfScope);
						if(varDecl == null)
							continue;
						FSMMachineInstance fsmInstance = fsm.creatInstance();
						fsmInstance.setRelatedASTNode(pExp);
						String desp = "";
						if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH)
						{
							desp = "The varibale \"" + varDecl.getImage()
									+ "\" which defines in line "
									+ varDecl.getNode().getBeginLine()
									+ " may lead to memory leak in line " + snode.getBeginLine();
							if (methodDecl != null)
							{
								desp += " in \"" + methodDecl.getImage() + "\"";
							}
						}
						else
							if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
							{
								desp = "在第 " + varDecl.getNode().getBeginLine()
										+ " 行定义的变量 \"" + varDecl.getImage() + "\"在 "
										+ node.getBeginLine() + "行";
								if (methodDecl != null)
								{
									desp += " 调用方法 \"" + methodDecl.getImage() + "\"可能造成内存泄漏";
								}
							}
						fsmInstance.setDesp(desp);
						fsmInstance.setRelatedVariable(varDecl);
						list.add(fsmInstance);
					}
				}
			}
			
		}
		
		return list;
	}
	
	public static boolean checkAllocError(List<SimpleNode> nodes, FSMMachineInstance fsmin)
	{
		for(SimpleNode snode : nodes)
		{
			if(fsmin.getRelatedASTNode() == snode)
			{
				VariableNameDeclaration varDecl = fsmin.getRelatedVariable();
				VexNode vNode = snode.getCurrentVexNode();
				if(vNode != null){
					vNode.setfsmCompute(true);
					Domain domain = vNode.getDomain(varDecl);
					vNode.setfsmCompute(false);
					if(domain!=null && domain instanceof PointerDomain)
					{
						PointerDomain pDomain = (PointerDomain)domain;
						HashSet<CType_AllocType> allocSet = pDomain.Type;
						if(allocSet.contains(CType_AllocType.heapType))
						{
							return true;
						}
					}
				}
			}
		}
		return false;
	}
	
	private static SourceFileScope findSourceFileScope(Scope scope)
	{
		Scope parent = scope;
		
		while(parent!=null && !(parent instanceof SourceFileScope))
		{
			parent = parent.getParent();
		}
		
		return (SourceFileScope)parent;
	}
}
