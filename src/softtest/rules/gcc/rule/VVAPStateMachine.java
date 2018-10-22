package softtest.rules.gcc.rule;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.*;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.AbstractExpression;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.Type.CType;
import softtest.symboltable.c.Type.CType_BaseType;
import softtest.symboltable.c.Type.CType;
import softtest.symboltable.c.Type.CType_BaseType;

/**
 * @author Void Variable As Parameter 禁止void类型的变量作为参数进行传递 (过程调用类)
 */
public class VVAPStateMachine {
	// 找到表达式中的函数使用节点
	private static String xpath = ".//PrimaryExpression[@Method='true']| .//PostfixExpression[@Method='true']";
	private static List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
	private static List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();

	public static List<FSMMachineInstance> createVVAPMachines(SimpleNode node,
			FSMMachine fsm) {

		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		SimpleNode args = null;
		List<SimpleNode> argsList = null;

		for (SimpleNode snode : evaluationResults) {
			// args=(ASTPostfixExpression)snode.getFirstParentOfType(ASTPostfixExpression.class).jjtGetChild(1);
			// 找出函数的参数节点,不包含f(func(a))中func(a)情况,只处理传入的是单个变量的情况
			ASTPostfixExpression post = (ASTPostfixExpression) snode.getFirstParentOfType(ASTPostfixExpression.class);
			if (post.jjtGetNumChildren() == 1)
				continue;
			args = (SimpleNode) post.jjtGetChild(1);
			argsList = StateMachineUtils.getEvaluationResults(args,"./AssignmentExpression/UnaryExpression/PostfixExpression[not(./ArgumentExpressionList )]/PrimaryExpression[@DescendantDepth='0']");
			if (argsList == null || argsList.size() == 0)
				continue;
			for (SimpleNode arg : argsList) {
				CType type = CType.getOrignType(((AbstractExpression) arg).getType()); // 得到最原始的type
				if (type != null && type == CType_BaseType.voidType) {
					VariableNameDeclaration variable = arg.getVariableNameDeclaration();
					addFSMDescription(snode, variable, fsm);
					break;
				}
			}
		}
		return list;
	}

	private static void addFSMDescription(SimpleNode node,
			VariableNameDeclaration variable, FSMMachine fsm) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		String varName = "";
		if (variable != null && variable.getImage() != null) {
			varName = variable.getImage();
		}

		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
			fsminstance.setDesp("Avoid using void type variable as function parameter. Using void type parameter may lead to unpredictable results.");
		} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE) {
			fsminstance.setDesp("禁止void类型的变量" + varName
					+ "作为参数进行传递。\r\n传递void类型的参数会导致不可预料的结果。");
		}
		list.add(fsminstance);
	}
}
