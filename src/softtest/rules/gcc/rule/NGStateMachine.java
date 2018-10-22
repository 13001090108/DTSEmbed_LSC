package softtest.rules.gcc.rule;

import java.util.*;

import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;

/**
 * @author LiuChang
 * NoGoto
 * 禁止使用goto语句
 **/
public class NGStateMachine {

	public static List<FSMMachineInstance> createNGStateMachines(SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		String xpath = "//JumpStatement[@Image='goto']";
		List<SimpleNode> result = StateMachineUtils.getEvaluationResults(node, xpath);
		
		for(Iterator<SimpleNode> itr = result.iterator(); itr.hasNext();) {
			SimpleNode jump = (SimpleNode) itr.next();
			
			addFSM(list,jump,fsm);
			}
		
		return list;
	}
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsmInstance = fsm.creatInstance();
		fsmInstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) 		
			fsmInstance.setDesp("NoGoto: It's a bad programing habit to use 'goto',which distroy the structure of the programe.so it's forbidden to use 'goto'");
		else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
			fsmInstance.setDesp("禁止使用goto语句: 使用goto语句是不好的编程习惯，破坏了程序的结构化，因此禁止使用goto语句。");
		list.add(fsmInstance);
	}
}
