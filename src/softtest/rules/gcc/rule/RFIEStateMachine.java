package softtest.rules.gcc.rule;

import java.util.*;

import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.*;



/** 
 * @author
 * Related Functions In Expression
 * 禁止同一个表达式中调用多个相关函数 (过程调用类)
 */

public class RFIEStateMachine {	
	//找到所有的赋值表达式
	private static String xpath = ".//Statement/ExpressionStatement/Expression/AssignmentExpression";
	//找到表达式中作为参数传递的变量（仅考虑传地址&a的情况）
	private static String xpath2 = ".//ArgumentExpressionList/AssignmentExpression/UnaryExpression/UnaryExpression/PostfixExpression/PrimaryExpression[@Method='false']";
	private static List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
	private static List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
	
	public static List<FSMMachineInstance> createRFIEMachines(SimpleNode node, FSMMachine fsm){
		
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);			
		for (SimpleNode snode : evaluationResults) {
			Set<VariableNameDeclaration> variables = new HashSet<VariableNameDeclaration>();//存放表达式调用的所有的变量(作为参数)
			List<SimpleNode> argList= new ArrayList<SimpleNode>();
			argList = StateMachineUtils.getEvaluationResults(snode, xpath2);
			
			for(SimpleNode arg: argList) {
				VariableNameDeclaration getVariableNameDeclaration = arg.getVariableNameDeclaration();
				if(getVariableNameDeclaration != null && variables.contains(getVariableNameDeclaration)) {	
					addFSMDescription(snode,fsm,getVariableNameDeclaration);
					break;
				}
				else if(getVariableNameDeclaration != null) {
					variables.add(getVariableNameDeclaration);
				}
			}
		}
	    return list;
	}	
	
	private static void addFSMDescription( SimpleNode node, FSMMachine fsm,VariableNameDeclaration variable ) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		fsminstance.setRelatedVariable(variable);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp("Forbid related functions in  one expression. If an expression is calling a number of related functions, it may be executed in a different order and produces different results.");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("禁止同一个表达式中调用多个相关函数。\r\n如果同一个表达式中调用多个相关函数，可能会因执行的顺序不同而产生不同的结果。");
			}	
		
		list.add(fsminstance);
	}
}
