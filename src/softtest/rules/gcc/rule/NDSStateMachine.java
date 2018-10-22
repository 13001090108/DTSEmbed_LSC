package softtest.rules.gcc.rule;

import java.util.*;

import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsm.c.*;
import softtest.rules.c.StateMachineUtils;

/**
 * @author zhouhb
 * No Default Switch
 * 4.3.1.4 在switch语句中必须有default语句
 **/
public class NDSStateMachine {
	
	public static List<FSMMachineInstance> createNDSStateMachines(SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		String xpath = ".//SelectionStatement[@Image='switch']";
		List<SimpleNode> result = StateMachineUtils.getEvaluationResults(node, xpath);
		
		for(Iterator itr = result.iterator(); itr.hasNext();) {
			ASTSelectionStatement selNode = (ASTSelectionStatement) itr.next();
			String defaultXpath = ".//LabeledStatement[@Image='default']";
			List<SimpleNode> defaultClause = StateMachineUtils.getEvaluationResults(selNode, defaultXpath);
			if(defaultClause.isEmpty())
				addFSM(list, selNode, fsm);
		}
		return list;
	}

	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsmInstance = fsm.creatInstance();
		fsmInstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) 		
			fsmInstance.setDesp("switch in line " + node.getBeginLine() + "has no default branch. Use default branch can show that all possibilities hava been concerned.");
		else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
			fsmInstance.setDesp("在第 "+node.getBeginLine()+" 行的switch语句没有default分支。" +
					"如果switch语句中缺省了default语句，当所有的case语句的表达式值都不匹配时，则会跳转到整个switch语句后的下一个语句执行。强制default语句的使用体现出已考虑了各种情况的编程思想。");
		list.add(fsmInstance);
	}
}
