package softtest.rules.gcc.rule;

import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.ASTAbstractDeclarator;
import softtest.ast.c.ASTCompoundStatement;
import softtest.ast.c.ASTDirectAbstractDeclarator;
import softtest.ast.c.ASTDirectDeclarator;
import softtest.ast.c.ASTFunctionDefinition;
import softtest.ast.c.ASTIterationStatement;
import softtest.ast.c.ASTParameterDeclaration;
import softtest.ast.c.ASTParameterList;
import softtest.ast.c.ASTPointer;
import softtest.ast.c.ASTSelectionStatement;
import softtest.ast.c.ASTStatement;
import softtest.ast.c.ASTTypeSpecifier;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.fsm.c.FSMRelatedCalculation;
import softtest.interpro.c.InterContext;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.Type.CType;

/**
 * @author 
 * @BWB means Block With Bracket
 * @1st:循环体必须用大括号括起来
 * @2nd:if/else中的语句必须用大括号括起来
 * @3th:main函数必须是int main(void)或int main (int, char*[])的形式
 */
public class BWBStateMachine {

	public static List<FSMMachineInstance> createBWBStateMachines(
			SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		//String xPath = ".//IterationStatement[not(@Image='do')]";
		String xPath = ".//IterationStatement";
		xPath += "|.//SelectionStatement";
		xPath += "|.//Declarator/DirectDeclarator[@Image='main']";
		List<SimpleNode> evaluationResults = StateMachineUtils
				.getEvaluationResults(node, xPath);
		for (SimpleNode snode : evaluationResults) {
			if(snode.getFileName()!=null&&snode.getFileName().toString().matches(InterContext.INCFILE_POSTFIX)){
				continue;
			}
			FSMMachineInstance fsminstance = fsm.creatInstance();
			fsminstance.setRelatedASTNode(snode);
			fsminstance.setRelatedObject(new FSMRelatedCalculation(snode));
			list.add(fsminstance);
		}
		return list;
	}

	public static boolean checkHasBracket(List<SimpleNode> nodes,
			FSMMachineInstance fsmin) {
		boolean result = false;
		SimpleNode simnode = fsmin.getRelatedASTNode();
		for (SimpleNode node : nodes) {
			if (simnode != node)
				continue;
			if (simnode instanceof ASTIterationStatement) {
				result = checkIteration(simnode, fsmin);
			} else if (simnode instanceof ASTSelectionStatement) {
				result = checkSelection(simnode, fsmin);
			} else if (simnode instanceof ASTDirectDeclarator) {
				result = checkMainFun(simnode, fsmin);
			}
		}
		return result;
	}

	private static boolean checkIteration(SimpleNode simnode,
			FSMMachineInstance fsmin) {
		boolean result = false;
		ASTIterationStatement iternode = (ASTIterationStatement) simnode;
		String name = iternode.getImage();
		ASTStatement stat = (ASTStatement) iternode
				.getFirstDirectChildOfType(ASTStatement.class);
		if (stat.jjtGetNumChildren() == 0
				|| (!(stat.jjtGetChild(0) instanceof ASTCompoundStatement))) {
			result = true;
			addFSMDescriptionIter(name, fsmin);
		}
		return result;
	}

	private static boolean checkSelection(SimpleNode simnode,
			FSMMachineInstance fsmin) {
		boolean result1 = false;
		boolean result2 = false;
		ASTSelectionStatement selnode = (ASTSelectionStatement) simnode;
		if (selnode.jjtGetNumChildren() <= 1)
			return false;
		if (selnode.jjtGetNumChildren() == 2) {
			ASTStatement stat1 = (ASTStatement) selnode.jjtGetChild(1);
			if (stat1.jjtGetNumChildren() == 0
					|| (!(stat1.jjtGetChild(0) instanceof ASTCompoundStatement))) {
				result1 = true;
				addFSMDescriptionSelect("if", fsmin);
			}
		} else if (selnode.jjtGetNumChildren() > 2) {
			ASTStatement stat1 = (ASTStatement) selnode.jjtGetChild(1);
			ASTStatement stat2 = (ASTStatement) selnode.jjtGetChild(2);
			if (stat1.jjtGetNumChildren() == 0
					|| (!(stat1.jjtGetChild(0) instanceof ASTCompoundStatement))) {
				result1 = true;
			}
			if (stat2.jjtGetNumChildren() == 0
					|| (!((stat2.jjtGetChild(0) instanceof ASTCompoundStatement) || (stat2
							.jjtGetChild(0) instanceof ASTSelectionStatement)))) {
				result2 = true;
			}
			String name = "";
			if (result1 && result2) {
				name = "if and else";
				addFSMDescriptionSelect(name, fsmin);
			} else if (result1) {
				name = "if";
				addFSMDescriptionSelect(name, fsmin);
			} else {
				name = "else";
				fsmin.setNodeUseToFindPosition(stat2);
				addFSMDescriptionSelect(name, fsmin);
			}
		}
		return result1 || result2;
	}

	private static boolean checkMainFun(SimpleNode simnode,
			FSMMachineInstance fsmin) {
		boolean result = false;
		ASTDirectDeclarator idnode = (ASTDirectDeclarator) simnode;
		// SimpleNode
		// declaratorNode=(SimpleNode)idnode.jjtGetParent().jjtGetChild(0);
		// String typeReturn=declaratorNode.getImage();
		ASTFunctionDefinition fun = (ASTFunctionDefinition) idnode
				.jjtGetParent().jjtGetParent();
		MethodNameDeclaration fundec = fun.getDecl();
		CType typeReturn = fundec.getType();
		if (!typeReturn.toString().endsWith("int")) {
			result = true;
			addFSMDescriptionMain(fsmin);
		} else {
			if (idnode.jjtGetNumChildren() == 0) {
				return false;
			} else if (idnode.containsChildOfType(ASTParameterList.class)) {
				ASTParameterList params = (ASTParameterList) idnode
						.jjtGetChild(0).jjtGetChild(0);
				int paranum = params.jjtGetNumChildren();
				if (paranum == 0) {
					return false;
				} else if (paranum == 1) {
					ASTTypeSpecifier param1type = (ASTTypeSpecifier) params
							.getFirstChildOfType(ASTTypeSpecifier.class);
					if (param1type.getImage().equals("void")) {
						return false;
					} else {
						result = true;
						addFSMDescriptionMain(fsmin);
					}
				} else if (paranum == 2) {
					ASTParameterDeclaration param1del = (ASTParameterDeclaration) params
							.jjtGetChild(0);
					ASTParameterDeclaration param2del = (ASTParameterDeclaration) params
							.jjtGetChild(1);
					ASTTypeSpecifier param1type = (ASTTypeSpecifier) param1del
							.getFirstChildOfType(ASTTypeSpecifier.class);
					ASTTypeSpecifier param2type = (ASTTypeSpecifier) param2del
							.getFirstChildOfType(ASTTypeSpecifier.class);
					if (param1type.getImage().equals("int")
							&& param2type.getImage().equals("char")) {
						if ((param2del.jjtGetNumChildren() == 2)
								&& (param2del
										.containsChildOfType(ASTAbstractDeclarator.class))) {
							ASTAbstractDeclarator absdecl1 = (ASTAbstractDeclarator) param2del
									.getFirstChildOfType(ASTAbstractDeclarator.class);
							if ((absdecl1.jjtGetNumChildren() == 2)
									&& absdecl1
											.containsChildOfType(ASTPointer.class)
									&& absdecl1
											.containsChildOfType(ASTDirectAbstractDeclarator.class)) {
								return false;
							} else {
								result = true;
								addFSMDescriptionMain(fsmin);
							}
						} else {
							result = true;
							addFSMDescriptionMain(fsmin);
						}
					} else
						result = true;
					addFSMDescriptionMain(fsmin);
				} else {
					result = true;
					addFSMDescriptionMain(fsmin);
				}
			}
		}
		// List<CType> paras=fundec.getParams();
		// if(fun.getParameterCount()==0)
		// return false;
		// if(fun.getParameterCount()!=2){
		// result=true;
		// }else{
		// CType para1=paras.get(0);
		// CType para2=paras.get(1);
		// if(!para1.getName().equals("int")){
		// result=true;
		// }else if(!(para2 instanceof CType_Pointer)){
		// result=true;
		// }else
		// if(!((CType_Pointer)para2).getOriginaltype().getName().equals("char")){
		// result=true;
		// }
		// }
		// }
		return result;
	}

	private static void addFSMDescriptionIter(String variable,
			FSMMachineInstance fsminstance) {

		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
			fsminstance.setDesp("Loop " + variable + " has not bracket.");
		} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE) {
			fsminstance.setDesp(variable + "循环体没有大括号。");
		}
	}

	private static void addFSMDescriptionSelect(String variable,
			FSMMachineInstance fsminstance) {
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
			fsminstance.setDesp("Selection " + variable + " has not bracket.");
		} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE) {
			fsminstance.setDesp(variable + "条件语句体没有大括号。");
		}
	}

	private static void addFSMDescriptionMain(FSMMachineInstance fsminstance) {
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
			fsminstance
					.setDesp("function main should have correct definition.");
		} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE) {
			fsminstance.setDesp("main函数定义不确切。");
		}
	}
}
