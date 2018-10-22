package softtest.rules.gcc.question;

import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.ASTCastExpression;
import softtest.ast.c.ASTConstant;
import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.fsm.c.FSMRelatedCalculation;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.Type.CType;
import softtest.symboltable.c.Type.CType_BaseType;

/**
 * @author
 * 应查找 /、<、<=、>、>= 运算符，查看其参数变量类型是否一致，如果不一致则应报错
 */

public class SUMUStateMachine {
	public static List<FSMMachineInstance> createSUMUStateMachines(
			SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();

		// 查询所有出现<、<=、>、>=、/运算符的结点
		String xPath = ".//MultiplicativeExpression[@Operators='/']|.//RelationalExpression";
		List<SimpleNode> evaluationResults = StateMachineUtils
				.getEvaluationResults(node, xPath);
		for (SimpleNode snode : evaluationResults) {
			FSMMachineInstance fsminstance = fsm.creatInstance();
			fsminstance.setRelatedASTNode(snode);
			fsminstance.setRelatedObject(new FSMRelatedCalculation(snode));
			list.add(fsminstance);
		}
		return list;

	}

	public static boolean checkexpression(List<SimpleNode> nodes,
			FSMMachineInstance fsmin) {
		boolean result = false;
		SimpleNode simnode = fsmin.getRelatedASTNode();
		for (SimpleNode node : nodes) {
			if (simnode != node)
				continue;
			CType c1 = null,c2 = null;
			if(simnode.jjtGetChild(0) instanceof ASTUnaryExpression){
			    ASTUnaryExpression unaryexp1 = (ASTUnaryExpression) simnode.jjtGetChild(0);
			    if(unaryexp1.containsChildOfType(ASTConstant.class))
			    	return false;
			    else
			    	c1 = (CType) unaryexp1.getType();
			    
			}else if(simnode.jjtGetChild(0) instanceof ASTCastExpression){
				ASTCastExpression unaryexp1 = (ASTCastExpression) simnode.jjtGetChild(0);
				if(unaryexp1.containsChildOfType(ASTConstant.class))
			    	return false;
			    else
			    	c1 = (CType) unaryexp1.getType();
			}
			if(simnode.jjtGetChild(1) instanceof ASTUnaryExpression){
			    ASTUnaryExpression unaryexp2 = (ASTUnaryExpression) simnode.jjtGetChild(1);
			    if(unaryexp2.containsChildOfType(ASTConstant.class))
			    	return false;
			    else
			    	c2 = (CType) unaryexp2.getType();
			}else if(simnode.jjtGetChild(1) instanceof ASTCastExpression){
				ASTCastExpression unaryexp2 = (ASTCastExpression) simnode.jjtGetChild(1);
				if(unaryexp2.containsChildOfType(ASTConstant.class))
			    	return false;
			    else
			    	c2 = (CType) unaryexp2.getType();
			}
			if(c1!=null&&c2!=null&&c1.isBasicType()&&c2.isBasicType()){
			if (c1.equals(c2)) {
				return false;
			} else if (c1.equalType(CType_BaseType.intType)
					&& c2.equalType(CType_BaseType.uIntType)
					|| c2.equalType(CType_BaseType.intType)
					&& c1.equalType(CType_BaseType.uIntType)
					|| c1.equalType(CType_BaseType.charType)
					&& c2.equalType(CType_BaseType.signedCharType)
					|| c2.equalType(CType_BaseType.charType)
					&& c1.equalType(CType_BaseType.signedCharType)
					|| c1.equalType(CType_BaseType.charType)
					&& c2.equalType(CType_BaseType.uCharType)
					|| c2.equalType(CType_BaseType.charType)
					&& c1.equalType(CType_BaseType.uCharType)
					|| c1.equalType(CType_BaseType.uCharType)
					&& c2.equalType(CType_BaseType.signedCharType)
					|| c2.equalType(CType_BaseType.uCharType)
					&& c1.equalType(CType_BaseType.signedCharType)
					|| c1.equalType(CType_BaseType.uLongLongType)
					&& c2.equalType(CType_BaseType.longLongType)
					|| c2.equalType(CType_BaseType.uLongLongType)
					&& c1.equalType(CType_BaseType.longLongType)
					|| c1.equalType(CType_BaseType.uLongType)
					&& c2.equalType(CType_BaseType.longType)
					|| c2.equalType(CType_BaseType.uLongType)
					&& c1.equalType(CType_BaseType.longType)
					|| c1.equalType(CType_BaseType.uShortType)
					&& c2.equalType(CType_BaseType.shortType)
					|| c2.equalType(CType_BaseType.uShortType)
					&& c1.equalType(CType_BaseType.shortType)) {

				result = true;
				addFSMDescription(fsmin);
			}
		}
			else{
				return false;
			}
		}
		return result;
	}

	// private static void checkExpression(List<SimpleNode> nodes, FSMMachine
	// fsm) {

	// }

	private static void addFSMDescription(FSMMachineInstance fsminstance) {
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH)
			fsminstance.setDesp("mixed use signed and unsigned type");
		else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
			fsminstance.setDesp("运算中出现了signed和unsigned的混用。"
					+ "signed与unsigned变量同时出现在 %、/、<、<=、>、>=运算中的时候，可能产生不期望的结果。");
	}
}