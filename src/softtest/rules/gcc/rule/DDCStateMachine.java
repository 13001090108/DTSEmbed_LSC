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
 * @author 
 * Design Dead Code (推荐类)
 * 避免由于设计的原因导致某些代码不能执行
 */
public class DDCStateMachine {	
	//找到if(0){...}的{...}语句
	private static String xpath = ".//SelectionStatement[@Image='if' and ./Expression[ not(.//PostfixExpression[@DescendantDepth='1']) and .//Constant[@Image='0']]]/Statement[1]";
	//找到if(1){}else{}的else{}语句块
	private static String xpath1 = ".//SelectionStatement[@Image='if' and ./Expression[ not(.//PostfixExpression[@DescendantDepth='1']) and .//Constant[@Image!='0'] ] ]/Statement[ position()=2 and not(./SelectionStatement)]";
	
	private static List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
	private static List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
	
	public static List<FSMMachineInstance> createDDCMachines(SimpleNode node, FSMMachine fsm){
		
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath + " | " + xpath1);	
		for (SimpleNode snode : evaluationResults) {
			addFSMDescription(snode,fsm);
		}
	    return list;
	}	

	private static void addFSMDescription( SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp("Avoid dead code caused by program design. As a judge of the condition is a constant value, thus some branch will never be executed.");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("避免由于设计的原因导致某些代码不能执行。\r\n该准则的违背通常表现为，做为判断的条件是一个常数值，因此使一些控制分支始终不可执行。");
			}	
		
		list.add(fsminstance);
	}
}

