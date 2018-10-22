package softtest.rules.gcc.question;

import java.util.*;

import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.*;
import softtest.symboltable.c.Type.CType;

/**
 * @author lrt
 */
public class LSStateMachine {

	public static List<FSMMachineInstance> createLSStateMachines(SimpleNode node, FSMMachine fsm){
	
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		String xpath = ".//PrimaryExpression[@Image='sleep']";
		List<SimpleNode> sleepResults = StateMachineUtils.getEvaluationResults(
				node, xpath);
		if (sleepResults.size() == 0)
			return null;
		else {
			List<SimpleNode> lockResults = null;
			String xpath1 = ".//UnaryExpression/PostfixExpression[./PrimaryExpression[@Image='pthread_mutex_lock']]";
			lockResults = StateMachineUtils.getEvaluationResults(node, xpath1);
			Iterator itr = lockResults.iterator();
			boolean lockSleep = false;
			while (itr.hasNext()) {
				SimpleNode snode = (SimpleNode) itr.next();
				String mutexImage = null;
				String mutexType=null;
				if (snode instanceof ASTPostfixExpression) {
					ASTPostfixExpression lockPostfix_expression = (ASTPostfixExpression) snode;
					if (lockPostfix_expression.jjtGetNumChildren() >= 2) {
						SimpleNode sn1 = (SimpleNode) lockPostfix_expression
								.jjtGetChild(1);
						if (sn1 != null
								&& sn1.getFirstChildOfType(ASTPrimaryExpression.class) != null) {
							ASTPrimaryExpression paramPrimaryExpression = (ASTPrimaryExpression) sn1
									.getFirstChildOfType(ASTPrimaryExpression.class);
							mutexImage = paramPrimaryExpression.getImage();
							mutexType=paramPrimaryExpression.getType().toString();
						}
					}
				} else
					continue;
				
				if (mutexImage != null) {
					String xpath2 = ".//UnaryExpression/PostfixExpression[./PrimaryExpression[@Image='pthread_mutex_unlock']][./ArgumentExpressionList//PostfixExpression/PrimaryExpression[@Image='" +
							 mutexImage + "' and @Type='" + mutexType + "']] ";
					List<SimpleNode> unlockResults = StateMachineUtils
							.getEvaluationResults(node, xpath2);

					if (unlockResults.size() != 0) {
						int lockBeginLine = snode.getBeginLine();
						MethodScope lockScope = snode.getScope()
								.getEnclosingMethodScope();
						Iterator itr1 = unlockResults.iterator();
						while (itr1.hasNext()) {
							SimpleNode unlockNode = (SimpleNode) itr1.next();
							MethodScope unlockScope = unlockNode.getScope()
									.getEnclosingMethodScope();
							if (lockScope.equals(unlockScope)) {
								int unlockBeginLine = unlockNode.getBeginLine();
								int min = lockBeginLine <= unlockBeginLine ? lockBeginLine
										: unlockBeginLine;
								int max = lockBeginLine < unlockBeginLine ? unlockBeginLine
										: lockBeginLine;
								Iterator itr2 = sleepResults.iterator();
								while (itr2.hasNext()) {
									SimpleNode sleepNode = (SimpleNode) itr2
											.next();
									if (sleepNode.getBeginLine() >= min
											&& sleepNode.getBeginLine() <= max) {
										lockSleep = true;
										break;
									}
								}
								if (lockSleep) {
									addFSM(snode, fsm,list);
									break;
								}
							}

						}
					}

				}
			}
		}
		return list;
	}
	private static void addFSM(SimpleNode node, FSMMachine fsm, List<FSMMachineInstance> list) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp(" Line "+node.getBeginLine()+":Block method used improperly in critical area.");
				} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
					fsminstance.setDesp("警告：第" + node.getBeginLine()
					+ "行在临界段内调用了阻塞函数。");
				}		
			list.add(fsminstance);
		}
}
