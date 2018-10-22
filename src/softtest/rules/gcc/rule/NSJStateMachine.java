package softtest.rules.gcc.rule;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;

/** 
 * @author LiuChang
 * 避免使用setjump/longjump
 * NoSetjumpLongjump
 * NSJ
 */

public class NSJStateMachine {

	public static List<FSMMachineInstance> createNSJStateMachines(SimpleNode node, FSMMachine fsm){
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = null;
		
		String xPath=".//Statement//AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression[@Image='longjmp'] | .//Statement//AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression[@Image='_setjmp']";
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);
		Iterator itr = evaluationResults.iterator();
		                                                                                                                                                                                                                                                                                                                                                                                                                                                
		while(itr.hasNext()){
			ASTPrimaryExpression id = (ASTPrimaryExpression)itr.next();
			
			addFSM(list,id,fsm);
			}
		return list;
		
  }
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp(" NoSetjumpLongjump: Using setjump/longjump will destroy the structrue of the program ,which will put down the portability of the program. ");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("避免使用setjump/longjump: setjump/longjump的使用会破坏程序的结构化，会造成移植性差，因此避免使用setjump/longjump。");
			}	
		
		list.add(fsminstance);
	}
}
