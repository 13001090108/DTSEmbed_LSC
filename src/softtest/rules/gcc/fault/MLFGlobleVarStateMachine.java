package softtest.rules.gcc.fault;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.Variable;
import softtest.rules.c.BasicStateMachine;
import softtest.rules.c.StateMachineUtils;
import softtest.summary.gcc.fault.MethodMMFeatureVisitor;
import softtest.summary.gcc.fault.MethodMMPreCondition;
import softtest.summary.gcc.fault.MethodMMPreConditionVisitor;
import softtest.symboltable.c.ClassScope;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.SourceFileScope;
import softtest.symboltable.c.VariableNameDeclaration;

/**
 * 
 */
public class MLFGlobleVarStateMachine extends BasicStateMachine
{

	@Override
	public void registFetureVisitors()
	{
		super.registFetureVisitors();
		InterContext.addSideEffectVisitor(MethodMMPreConditionVisitor
				.getInstance());
	}

	public static List<FSMMachineInstance> createMLFStateMachines(
			SimpleNode node, FSMMachine fsm)
	{
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();

		/*String xPath = ".//statement_list/statement/expression/assignment_expression[./assignment_expression/pm_expression/unary_expression/postfix_expression/primary_expression/new_expression]/pm_expression//id_expression";

		List<SimpleNode> evaluationResults = StateMachineUtils
				.getEvaluationResults(node, xPath);
		Iterator itr = evaluationResults.iterator();
		while (itr.hasNext())
		{
			ASTid_expression idExpression = (ASTid_expression) itr.next();
			if (!(idExpression.getType() instanceof CPPType_Pointer))
				continue;
			// ExpressionDomainVisitor exp = new ExpressionDomainVisitor();
			// Object re = exp.visit((SimpleNode)idExpression, new
			// DomainData(false));
			// if (!(re instanceof VariableNameDeclaration))
			// continue;
			// VariableNameDeclaration varDec = (VariableNameDeclaration)re;
			VariableNameDeclaration varDec = idExpression.getVariable();
			if (varDec == null)
				continue;
			if (varDec.getScope() instanceof ClassScope
					|| varDec.getScope() instanceof SourceFileScope)
			{ // 是否为全局或者类成员变量
				addFSM(fsm, idExpression, varDec, list);
			}
		}*/

//		xPath = ".//postfix_expression/primary_expression/id_expression[@Method='true']|.//declaration/declaration_specifiers/qualified_type/qualified_id[@Method='true']";
		
		String xPath = ".//UnaryExpression/PostfixExpression/PrimaryExpression[@Method='true']";
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);
		Iterator itr = evaluationResults.iterator();
		while (itr.hasNext())
		{
			SimpleNode snode = (SimpleNode) itr.next();
			MethodNameDeclaration methodDecl = StateMachineUtils
					.getMethodNameDeclaration(snode);
			if (methodDecl != null && methodDecl.getImage().equals("malloc"))
			{
				VariableNameDeclaration varDecl = MethodMMFeatureVisitor
						.findAssginDeclInQual(snode);
				if (varDecl != null
						&& (varDecl.getScope() instanceof SourceFileScope || varDecl
								.getScope() instanceof ClassScope))
				{
					addFSM(fsm, snode, varDecl, list);
				}
			}
		}
		return list;
	}

	public static boolean checkNewMethod(List<SimpleNode> nodes,
			FSMMachineInstance fsmin)
	{
		for (SimpleNode snode : nodes)
		{
			MethodNameDeclaration methodDecl = StateMachineUtils
					.getMethodNameDeclaration(snode);
			if (methodDecl == null)
				continue;
			if (methodDecl.getMethodSummary() == null)
				continue;
			MethodMMPreCondition mmPreCondition = (MethodMMPreCondition) methodDecl
					.getMethodSummary().findMethodFeature(
							MethodMMPreCondition.class);
			if (mmPreCondition == null)
			{
				continue;
			}
			Variable var = fsmin.getRelatedVariable().getVariable();
			if (mmPreCondition.contains(fsmin.getRelatedVariable()))
			{
				String desp = fsmin.getDesp();
				desp += mmPreCondition.getDespString(var);
				fsmin.setDesp(desp);
				return true;
			}
		}
		return false;
	}

	private static void addFSM(FSMMachine fsm, SimpleNode idExpression,
			VariableNameDeclaration varDecl, List<FSMMachineInstance> list)
	{
		FSMMachineInstance fsmInstance = fsm.creatInstance();
		fsmInstance.setRelatedVariable(varDecl);
		fsmInstance.setRelatedASTNode(idExpression);
		String desp = "";
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH)
		{
			desp = "The globle varibale \"" + varDecl.getImage()
					+ " is allocated memory at line "
					+ idExpression.getBeginLine();

		}
		else
			if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
			{
				desp = "全局变量 \"" + varDecl.getImage() + "\"在第"
						+ idExpression.getBeginLine() + "行分配了内存";
			}
		fsmInstance.setDesp(desp);
		list.add(fsmInstance);
	}
}