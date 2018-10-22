package softtest.rules.gcc.rule;

import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.ASTArgumentExpressionList;
import softtest.ast.c.ASTDeclaration;
import softtest.ast.c.ASTDeclarationSpecifiers;
import softtest.ast.c.ASTDirectDeclarator;
import softtest.ast.c.ASTInitDeclaratorList;
import softtest.ast.c.ASTParameterDeclaration;
import softtest.ast.c.ASTPointer;
import softtest.ast.c.ASTStructDeclarationList;
import softtest.ast.c.ASTStructOrUnion;
import softtest.ast.c.ASTStructOrUnionSpecifier;
import softtest.ast.c.ASTTypeSpecifier;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.fsm.c.FSMRelatedCalculation;
import softtest.interpro.c.InterContext;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.VariableNameDeclaration;

/**
 * @author
 * @DNP means Declaration Not Proper
 * @1st: 字符型变量必须明确定义是有符号还是无符号
 * @2nd: 结构体变量声明应该完整
 * @3RD: 结构体声明中不能含有空域
 */
public class DNPStateMachine {

	public static List<FSMMachineInstance> createDNPStateMachines(
			SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		String xPath = ".//Declaration/DeclarationSpecifiers/TypeSpecifier[@Image='char']";
		xPath += "|.//TypeSpecifier/StructOrUnionSpecifier/StructOrUnion[@Image='struct']";

		List<SimpleNode> evaluationResults = StateMachineUtils
				.getEvaluationResults(node, xPath);
		for (SimpleNode snode : evaluationResults) {
			if (snode.getFileName() != null
					&& snode.getFileName().toString().matches(
							InterContext.INCFILE_POSTFIX)) {
				continue;
			}
			FSMMachineInstance fsminstance = fsm.creatInstance();
			fsminstance.setRelatedASTNode(snode);
			fsminstance.setRelatedObject(new FSMRelatedCalculation(snode));

			list.add(fsminstance);
		}
		return list;
	}

	public static boolean checkDeclaration(List<SimpleNode> nodes,
			FSMMachineInstance fsmin) {
		boolean result = false;
		SimpleNode simnode = fsmin.getRelatedASTNode();
		for (SimpleNode node : nodes) {
			if (simnode != node)
				continue;
			if (simnode instanceof ASTTypeSpecifier) {
				result = checkCharDecl(simnode, fsmin);
			} else if (simnode instanceof ASTStructOrUnion) {
				result = checkStruct(simnode, fsmin);
			}
		}
		return result;
	}

	public static boolean checkCharDecl(SimpleNode simnode,
			FSMMachineInstance fsmin) {
		boolean result = false;
		ASTDeclarationSpecifiers decl_sp = (ASTDeclarationSpecifiers) simnode
				.jjtGetParent();
		if (decl_sp.jjtGetParent() instanceof ASTDeclarationSpecifiers) {
			return false;
		} else {
			ASTDeclaration decl = (ASTDeclaration) decl_sp.jjtGetParent();
			ASTInitDeclaratorList initdecl = (ASTInitDeclaratorList) decl
					.jjtGetChild(1);
			SimpleNode temp = (SimpleNode) initdecl.jjtGetChild(0).jjtGetChild(
					0).jjtGetChild(0);
			if (temp instanceof ASTPointer) {
				return false;
			}
			if (temp instanceof ASTDirectDeclarator) {
				ASTDirectDeclarator varnode = (ASTDirectDeclarator) temp;
				VariableNameDeclaration varname = (VariableNameDeclaration) varnode
						.getDecl();
				result = true;
				addFSMDescriptionCharDecl(varname, fsmin);
			}
		}
		return result;
	}

	public static boolean checkStruct(SimpleNode simnode,
			FSMMachineInstance fsmin) {
		ASTStructOrUnionSpecifier structspecifier = (ASTStructOrUnionSpecifier) simnode
				.getFirstParentOfType(ASTStructOrUnionSpecifier.class);
		boolean result = false;
		if(structspecifier.getImage() == null){
			result = true;
			String varname = null;
			addFSMDescriptionStruct(varname, fsmin);
		}
		else if(structspecifier.containsParentOfType(ASTDeclaration.class)){
			ASTDeclaration decl = (ASTDeclaration) structspecifier.getFirstParentOfType(ASTDeclaration.class);
		    if(decl.jjtGetNumChildren()==1){
		    	if((!structspecifier.containsChildOfType(ASTStructDeclarationList.class))&&(!decl.containsChildOfType(ASTStructDeclarationList.class))){
		    		result = true;
					String varname = null;
					addFSMDescriptionStruct(varname, fsmin);
		    	}
		    }
		    if(decl.jjtGetNumChildren()==2){
		    	if(!(decl.jjtGetChild(1) instanceof ASTInitDeclaratorList)){
		    		result = true;
					String varname = null;
					addFSMDescriptionStruct(varname, fsmin);
		    	}
		    }
		}
		else{
			return false;
		}
//		if ((structspecifier.getImage() != null)
//				&& (structspecifier
//						.containsChildOfType(ASTStructDeclarationList.class))) {
//			return false;
//		}
//		if ((structspecifier.getImage() != null)
//				&& (structspecifier.containsParentOfType(ASTDeclaration.class))) {
//			ASTDeclaration decl = (ASTDeclaration) structspecifier
//					.getFirstParentOfType(ASTDeclaration.class);
//			if (decl.containsChildOfType(ASTInitDeclaratorList.class)) {
//				return false;
//			} else {
//				return true;
//			}
//		} else if ((structspecifier.containsParentOfType(ASTParameterDeclaration.class))||
//				(structspecifier.containsParentOfType(ASTArgumentExpressionList.class))) {
//			return false;
//		} else {
//			if (structspecifier.getImage() == null) {
//				result = true;
//				String varname = structspecifier.getImage();
//				addFSMDescriptionStruct(varname, fsmin);
//			} else if (!structspecifier
//					.containsChildOfType(ASTStructDeclarationList.class)) {
//				result = true;
//				String varname = structspecifier.getImage();
//				addFSMDescriptionStruct(varname, fsmin);
//			} else {
//				return false;
//			}
//		}
        
		return result;
	}

	private static void addFSMDescriptionCharDecl(
			VariableNameDeclaration variable, FSMMachineInstance fsminstance) {
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
			fsminstance.setDesp("Char variable " + variable.getImage()
					+ " should be explicit declared unsigned or signed");
		} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE) {
			fsminstance.setDesp("字符变量" + variable.getImage() + "应该显式声明为是否有符号");
		}
	}

	private static void addFSMDescriptionStruct(String variable,
			FSMMachineInstance fsminstance) {
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
			fsminstance.setDesp("Struct variable " + variable
					+ " should be not null");
		} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE) {
			fsminstance.setDesp("结构体变量" + variable + "没有完整的声明。");
		}
	}

}