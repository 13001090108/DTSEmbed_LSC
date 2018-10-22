package softtest.rules.gcc.rule;

import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.SimpleNode;
import softtest.ast.c.ASTAssignmentExpression;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;

/**
 * @author xiangwentao
 * Avoid Some Operation
 * 避免使用“+=”或“-=”或“+=”或“--”操作符  (推荐类)
 * (语句使用类)
 * 
 * “++”或“--”一般只在一个单独的表达式或循环控制中使用
 */
public class ASOStateMachine {
	
	private enum Type {TYPE_1, TYPE_2}
	
	public static List<FSMMachineInstance> createASOMachines(SimpleNode node, FSMMachine fsm){
		/**查询所有出现'+='与'-='的表达式*/
		String xPath = ".//Statement//Expression/AssignmentExpression/AssignmentOperator[@Operators='+=' or @Operators='-=']";
		/**查询所有出现'++'与'--'的表达式,前缀和后缀*/
		String xPath_1 = ".//UnaryExpression[@Operators='++' or @Operators='--'] | .//PostfixExpression[@Operators='++' or @Operators='--'] ";
		
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
		
		//查询所有出现'+='与'-='的表达式
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);
		for (SimpleNode snode : evaluationResults) {
			addFSMDescription(snode, fsm, Type.TYPE_1, list);
		}
		
		//查询所有出现'++'与'--'的表达式,前缀和后缀
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath_1);
		for (SimpleNode snode : evaluationResults) {
			//1.	去掉单独的表达式类型，如a++;
			//2.	去掉出现在for循环的动作节点，如for(i=0; i<10; i++){}
			SimpleNode parent = (SimpleNode) snode.getFirstParentOfType(ASTAssignmentExpression.class, node);
			SimpleNode ancestor = (SimpleNode) parent.getFirstParentOfType(ASTAssignmentExpression.class, node);
			if(ancestor != null)
				addFSMDescription(snode, fsm, Type.TYPE_2, list);
		}
		return list;
	}
	
	private static void addFSMDescription(SimpleNode node, FSMMachine fsm, Type type, List<FSMMachineInstance> list) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		if(type == Type.TYPE_1) {
			if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp("Avoid Some Operation, such as ‘+=’ and '-='");
			} 
			else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("避免使用“+=”或“-=”操作符。\r\n“+=”或“-=”操作符使用简洁，但也影响了可读性，容易出现编程失误。");
			}	
		}
		if(type == Type.TYPE_2) {
			if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp("Avoid Some Operation, such as ‘++’ and '--'");
			} 
			else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("避免使用“++”或“--”操作符。\r\n在表达式中使用这些操作符是很危险的，一般只在一个单独的表达式或循环控制中使用它。");
			}
		}
		list.add(fsminstance);
	}
}
