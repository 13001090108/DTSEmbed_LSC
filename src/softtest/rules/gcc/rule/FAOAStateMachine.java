package softtest.rules.gcc.rule;

import java.util.LinkedList;
import java.util.List;
import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;

/** 
 * @author LiuChang
 * Forbid Assignment Operator Abuse
 * 禁止在非赋值表达式中出现赋值操作符(如if(a=1), while(a=0), do{}while(a=0)中的误用)
 */
public class FAOAStateMachine {
	//找到if、while、do-while、switch、？：条件语句中的赋值表达式（仅指“=”操作符）节点
	private static String xpath1 = ".//SelectionStatement[@Image='if' or @Image='switch']/Expression/AssignmentExpression[./AssignmentOperator[@Operators='='] and ./UnaryExpression and ./AssignmentExpression]";
	private static String xpath2 = ".//IterationStatement[@Image='while' or @Image='do']/Expression/AssignmentExpression[./AssignmentOperator[@Operators='='] and ./UnaryExpression and ./AssignmentExpression]";
	private static String xpath3 = ".//ConditionalExpression/UnaryExpression/PostfixExpression/PrimaryExpression/Expression/AssignmentExpression[.AssignmentOperator[@operators'='] and ./UnaryExpression and ./AssignmentExpression]]";
	private static String xpath = xpath1 + " | " + xpath2 + " | " + xpath3;
	
	private static List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
	private static List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
	
	public static List<FSMMachineInstance> createFAOAMachines(SimpleNode node, FSMMachine fsm){	
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		
		for(SimpleNode snode: evaluationResults) {
			addFSMDescription(snode, fsm);
		}	

	return list;
	}	

	
	private static void addFSMDescription( SimpleNode node,  FSMMachine fsm) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp("Forbid assignment operator abuse in unassignment expression. It will produce an unexpected result.");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("禁止在非赋值表达式中出现赋值操作符。\r\n这会引起无法预料的后果，一般是由于将“=”误写为“==”造成的。");
			}		
		list.add(fsminstance);
	}
}
