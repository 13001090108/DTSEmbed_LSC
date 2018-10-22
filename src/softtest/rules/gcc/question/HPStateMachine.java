package softtest.rules.gcc.question;

import java.util.*;

import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.*;
import softtest.symboltable.c.Type.CType;

/*
 * @author lrt
 * HP Hidden Param 参数与局部变量同名
 */
public class HPStateMachine {

	public static List<FSMMachineInstance> createHPStateMachines(
			SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> paramResults = null;
		if (node instanceof ASTFunctionDefinition) {
			String xpath = ".//ParameterTypeList/ParameterList/ParameterDeclaration";
			paramResults = StateMachineUtils.getEvaluationResults(node, xpath);

			Iterator<SimpleNode> itr = paramResults.iterator();
			String paramImage = null;
			CType paramType = null;
			while (itr.hasNext()) {
				SimpleNode sNode = (SimpleNode) itr.next();
				if (sNode.getFirstChildOfType(ASTDirectDeclarator.class) != null) {
					ASTDirectDeclarator dd = (ASTDirectDeclarator) sNode
							.getFirstChildOfType(ASTDirectDeclarator.class);
					VariableNameDeclaration param = dd
							.getVariableNameDeclaration();
					if (param.isParam()) {
						paramImage = param.getImage();
						paramType = param.getType();
					}
				}
				if (paramImage != null) {
					String xpath1 = " .//Statement/Declaration/InitDeclaratorList/InitDeclarator/Declarator[@Image='"
							+ paramImage + "']";
					List<SimpleNode> evaluationResults = StateMachineUtils
							.getEvaluationResults(node, xpath1);

					Iterator<SimpleNode> itr1 = evaluationResults.iterator();
					while (itr1.hasNext()) {
						ASTDeclarator d1 = (ASTDeclarator) itr1.next();
						VariableNameDeclaration localVar = d1
								.getVariableNameDeclaration();
						if (localVar.getScope() instanceof LocalScope)
							if (localVar.getType().equals(paramType))
								addFSM(list, d1, fsm);

					}
				}
			}
		}

		return list;
	}

	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node,
			FSMMachine fsm) {
		FSMMachineInstance fsmInstance = fsm.creatInstance();
		fsmInstance.setRelatedASTNode(node);

		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH)
			fsmInstance.setDesp("Warning: Line" + node.getBeginLine()
					+ " local variable " + node.getImage()
					+ "has the same name with a function parameter");
		else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
			fsmInstance.setDesp("警告：第" + node.getBeginLine() + " 行局部变量"
					+ node.getImage() + "与函数参数同名");

		list.add(fsmInstance);
	}
}
