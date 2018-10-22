package softtest.rules.gcc.rule;

import java.util.*;

import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;

/**
 * @author suntao
 * Blank case
 * 4.3.1.8 禁止switch的case语句中无任何可执行语句 
 **/
public class BCStateMachine {

	public static List<FSMMachineInstance> createBCStateMachines(SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		String xpath = ".//LabeledStatement[@Image='case']";
		List<SimpleNode> result = StateMachineUtils.getEvaluationResults(node, xpath);
	
		
		for(Iterator<SimpleNode> itr = result.iterator(); itr.hasNext();) {
			SimpleNode statement = (ASTLabeledStatement) itr.next();
			SimpleNode childStatement = statement;
			do {
				if(childStatement != statement) {
					addFSM(list, statement, fsm);
					statement = childStatement;
				}
				
				if(childStatement.jjtGetChild(0) instanceof ASTStatement)
					childStatement = (SimpleNode) childStatement.jjtGetChild(0).jjtGetChild(0);
				else if(childStatement.jjtGetChild(1) instanceof ASTStatement)
					childStatement = (SimpleNode) childStatement.jjtGetChild(1).jjtGetChild(0);
			}while(childStatement != null && (childStatement.getImage().equals("case") || childStatement.getImage().equals("default")));
		}
		
		return list;
	}
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsmInstance = fsm.creatInstance();
		fsmInstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) 		
			fsmInstance.setDesp("case in line " + node.getBeginLine() + "is blank. Avoid to use this.");
		else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
			fsmInstance.setDesp("在第 "+node.getBeginFileLine()+" 行的case语句无可执行语句。" +
					"如果某个case语句中无任何可执行语句，则它将共享后面case语句中的执行语句。这种情况或是由于代码不完整造成的，或是编程者特意设计的。为了防止残留不完整的代码，因此禁止switch的case语句中无任何可执行语句。");
		list.add(fsmInstance);
	}
}
