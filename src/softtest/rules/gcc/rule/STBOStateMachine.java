package softtest.rules.gcc.rule;

import java.util.LinkedList;
import java.util.List;


import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.*;
import softtest.symboltable.c.Type.*;


/** 
 * @author nieminhui
 * Signed Type Bit Operator
 * 禁止对有符号类型使用位运算(char类型暂不当符号数对待，书上说根据编译器而定)
 * (运算处理类)
 */
public class STBOStateMachine {
	
	private static List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
	private static List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
	
	public static List<FSMMachineInstance> createSTBOMachines(SimpleNode node, FSMMachine fsm){
		
		//1：	找到所有的按位运算表达式&  |  ^
		//add by nieminhui
		//2011.3.2
		//找到所有的按位运算表达式&=, |=, ^=
		String xpath1 = ".//ANDExpression[count(child::UnaryExpression)=2] | .//InclusiveORExpression[count(child::UnaryExpression)=2] | .//ExclusiveORExpression[count(child::UnaryExpression)=2] " +
	      "| .//AssignmentExpression[./AssignmentOperator[@Operators='&='] | ./AssignmentOperator[@Operators='|='] | ./AssignmentOperator[@Operators='^=']]";
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath1);			
		for (SimpleNode snode : evaluationResults) {	
			List<SimpleNode> childs = StateMachineUtils.getEvaluationResults(snode, ".//UnaryExpression");
			ASTUnaryExpression child1 = (ASTUnaryExpression) childs.get(0);
			ASTUnaryExpression child2 = (ASTUnaryExpression) childs.get(1);

			boolean leftConstant = isConstant(child1);
			boolean rightConstant = isConstant(child2);

			if(leftConstant && rightConstant) //如果两数均为常数
				continue;
			if(!leftConstant && isSignedType(child1)) { //如果child1为有符号数且非常数			
				addFSMDescription(snode, fsm);
			}else if(!rightConstant && isSignedType(child2)) {//如果child2为有符号数且非常数
				addFSMDescription(snode, fsm);
			}
		}
		
		//2:	找到所有的按位运算表达式 ~
		String xpath2 = ".//UnaryExpression[./UnaryOperator[@Operators='~']]/UnaryExpression";
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath2);			
		for (SimpleNode snode : evaluationResults) {	
			if(!isConstant(snode) && isSignedType((ASTUnaryExpression)snode)) {
				addFSMDescription(snode, fsm);
			}
		}
		
		//3:  	找到所有的按位运算表达式移位表达式
		//关于有符号数的移位有一个单独的模式SVSO处理，这里就没有处理
	    return list;
	}	

	// 判断UnaryExpression是否为有符号类型的非常数	 
	private static boolean isSignedType(AbstractExpression node) {
		//add by nieminhui
		//2011.3.15		
		while(node.getImage() == "" )
		{
			List<SimpleNode> childs = StateMachineUtils.getEvaluationResults(node, ".//UnaryExpression");
			node = (AbstractExpression) childs.get(0);
		}		
		if(isConstant(node))
			return false;
		CType type = node.getType();
		if(type == CType_BaseType.intType || type == CType_BaseType.shortType || type == CType_BaseType.longType || type == CType_BaseType.longLongType /* || type == CType_BaseType.charType*/ ) 
			return true;
		else 
			return false;
	}

	// 判断UnaryExpression是否为常数
	private static boolean isConstant(SimpleNode node) {
		String xpath = ".//PostfixExpression/PrimaryExpression/Constant";
		List<SimpleNode> result = StateMachineUtils.getEvaluationResults(node, xpath);		
		if(result==null || result.size()==0)
			return false;
		return true;
	}

	private static void addFSMDescription( SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp("Forbit Bit Operator on Signed Type.Itis very dangerous using bit operation on signed number, because the sign bit will be wrong to change.");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("禁止对有符号类型使用位运算。\r\n位运算对有符号的数是很危险的，因为符号位会被错误地改变。");
			}	
		
		list.add(fsminstance);
	}
}
