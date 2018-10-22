package softtest.rules.gcc.rule;

import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.ASTConstant;
import softtest.ast.c.ASTTypeName;
import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.SimpleNode;
import softtest.ast.c.ASTCastExpression;
import softtest.ast.c.AbstractExpression;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.Type.CType_AbstPointer;

/** 
 * @author xiangwentao
 * 对指针变量使用强制类型转换赋值
 * CastToPointer
 */
public class CTPStateMachine {
	public static List<FSMMachineInstance> createCTPStateMachines(SimpleNode node, FSMMachine fsm){
		
		String xPath = ".//CastExpression";
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);
		
		for(SimpleNode snode : evaluationResults) {
			ASTCastExpression castExp = (ASTCastExpression)snode;
			if(castExp.jjtGetNumChildren() != 2)
				continue;
			ASTTypeName typeName = (ASTTypeName)castExp.jjtGetChild(0);
			ASTUnaryExpression unary = (ASTUnaryExpression)castExp.getFirstChildInstanceofType(ASTUnaryExpression.class);
			if(typeName.getType() == null || unary.getType() == null)
				continue;
			if(typeName.getType() instanceof CType_AbstPointer){
				if(!(unary.getType() instanceof CType_AbstPointer) ){
					if(unary.getType().toString().contains("pointer"))
						continue;
					SimpleNode cons = (SimpleNode)unary.getFirstChildOfType(ASTConstant.class);
					if(cons != null && cons.getImage().equals("0"))
						continue;
					addFSM(list,castExp,fsm,unary);
				}
			}
		}
		return list;
	}
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm,AbstractExpression ua) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp("CastToPointer: It's dangerous to cast other type to pointer,so casting from other to pointer should be avoided");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("对指针变量使用强制类型转换赋值: 强制将其它类型"+ua.getType().toString()+"转换为指针类型是很危险的，因此禁止对指针变量使用强制类型转换赋值。");
			}	
		
		list.add(fsminstance);
	}
}
