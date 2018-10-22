package softtest.rules.gcc.question;



import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;


/** 
 * @author YangRui
 * 
 */

public class BBUStateMachine {
	public static List<FSMMachineInstance> createBBUStateMachines(SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = null;
		
		String xpath = ".//AdditiveExpression | .//MultiplicativeExpression | .//ANDExpression | .//ExclusiveORExpression | .//InclusiveORExpression";
		
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		Iterator itr = evaluationResults.iterator();
	
		while(itr.hasNext()) {
			AbstractExpression astExpression = (AbstractExpression) itr.next();
			int n = astExpression.jjtGetNumChildren();
			AbstractExpression exp[] = new AbstractExpression[n];
			for(int i = 0; i < n; i++)
				exp[i] = (AbstractExpression) astExpression.jjtGetChild(i);
			for( ; n > 0; n--) {	
				if(exp[n - 1].getType()!= null && (exp[n - 1].getType().toString().equals("_Bool")||(exp[n - 1].getType().toString().equals("bool"))) ){
					//AbstractExpression state;
					ASTStatement state=(ASTStatement)exp[n - 1].getFirstParentOfType(ASTStatement.class);
					//state=exp[n-1];
					addFSM(list,state,fsm);
				}
			}
		}
		return list;
	}
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsmInstance = fsm.creatInstance();
		fsmInstance.setRelatedASTNode(node);
		
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) 		
			fsmInstance.setDesp("bool type bad use");
		else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
			fsmInstance.setDesp("警告：运算中出现了布尔类型的不良使用。" +
					"算术运算符（+ - * / %）和位逻辑运算符（^ &）的参数一般情况下不应该为布尔量。");
		
		list.add(fsmInstance);
	}
}
