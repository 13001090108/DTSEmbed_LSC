package softtest.rules.gcc.rule;

import java.util.*;

import softtest.ast.c.ASTLabeledStatement;
import softtest.ast.c.ASTStatement;
import softtest.ast.c.ASTStatementList;
import softtest.ast.c.SimpleNode;
import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.fsm.c.*;
import softtest.rules.c.StateMachineUtils;

/**
 * @author zhouhb
 * No Break Case
 * 4.3.1.7 禁止switch的case语句不是由break(或return)终止
 **/
public class NBCStateMachine {
	
	public static List<FSMMachineInstance> createNBCStateMachines(SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		String xpath = ".//SelectionStatement[@Image='switch']/Statement/CompoundStatement/StatementList/Statement[/LabeledStatement[@Image='case']]";
		List<SimpleNode> result = StateMachineUtils.getEvaluationResults(node, xpath);
		
		for(Iterator<SimpleNode> itr = result.iterator(); itr.hasNext();) {
			ASTStatement statement = (ASTStatement) itr.next();
			checkEndWithBreak(list, statement, fsm);
		}
		return list;
	}
	
	private static void checkEndWithBreak(List<FSMMachineInstance> list, SimpleNode statement, FSMMachine fsm) {
		SimpleNode childStatement = statement;
		do {
			if(childStatement.jjtGetChild(0) instanceof ASTLabeledStatement)
				childStatement = (SimpleNode) childStatement.jjtGetChild(0);
			else if(childStatement.jjtGetChild(0) instanceof ASTStatement)
				childStatement = (SimpleNode) childStatement.jjtGetChild(0);
			else if(childStatement.jjtGetChild(1) instanceof ASTStatement)
				childStatement = (SimpleNode) childStatement.jjtGetChild(1);
		}while(childStatement != null && (childStatement.getImage().equals("case") || childStatement.getImage().equals("default")));
		
		if(isEndWithBreak(childStatement))
			return;
		else {
			ASTStatementList stateList = (ASTStatementList) statement.getFirstParentOfType(ASTStatementList.class);
			int n = stateList.jjtGetNumChildren();
			int index = 0;
			for(int i = 0; i < n; i++) {
				if(stateList.jjtGetChild(i).equals(statement)) {
					index = i;
					break;
				}
			}
			if(index == n - 1)	
				return;					//最后一个case若没有break终结不报错
			else {
				for(int i = index + 1; i < n; i++) {
					ASTStatement nextStatement = (ASTStatement) stateList.jjtGetChild(i);
					if(isEndWithBreak(nextStatement))
						return;
					else if(i == n - 1)
						return;
					else {
						//modified by zhouhb
						//2011.3.1
//						ASTStatement next2 = (ASTStatement) stateList.jjtGetChild(i + 1);
//						if(next2.getImage().equals("case") || next2.getImage().equals("default")) {
						if(nextStatement.jjtGetChild(0)instanceof ASTLabeledStatement){
							ASTLabeledStatement label=(ASTLabeledStatement)nextStatement.jjtGetChild(0);
							if(label.getImage().equals("case")||label.getImage().equals("default"))
							addFSM(list, statement, fsm);
							return;
						}
					}
				}
			}
		}
	}
	
	private static boolean compoundIsEndWithBreak(SimpleNode stateList) {
		int n = stateList.jjtGetNumChildren();
		for(int i = 0; i < n; i++) {
			ASTStatement statement = (ASTStatement) stateList.jjtGetChild(i);
			if(isEndWithBreak(statement))
				return true;
			else if(i == n - 1)
				return false;
		}
		return true;
	}
	
	private static boolean isEndWithBreak(SimpleNode node) {
//		if(node.getImage().equals("break") || node.getImage().equals("return") || 
//				node.getImage().equals("goto") || node.getImage().equals("continue"))
//			return true;
		//modified by zhouhb
		//2011.3.1
		if(node.jjtGetChild(0)instanceof ASTJumpStatement){
			ASTJumpStatement jump=(ASTJumpStatement)node.jjtGetChild(0);
			if(jump.getImage().equals("break") || jump.getImage().equals("return") || 
					jump.getImage().equals("goto") || jump.getImage().equals("continue")|| jump.getImage().equals("exit"))
				return true;
		}else if(node.containsChildOfType(ASTPrimaryExpression.class)){
			ASTPrimaryExpression pri=(ASTPrimaryExpression)node.getFirstChildOfType(ASTPrimaryExpression.class);
			if(pri.getImage().equals("exit"))
				return true;
		}
		
		if(node.jjtGetNumChildren() == 0)
			return false;
		if(node.jjtGetChild(0) instanceof ASTCompoundStatement)
			return compoundIsEndWithBreak((ASTStatementList)(node.jjtGetChild(0).jjtGetChild(0)));
		if(node.jjtGetChild(0) instanceof ASTExpressionStatement)
			return false;
		if(node.jjtGetChild(0) instanceof ASTSelectionStatement) {
			ASTSelectionStatement selNode = (ASTSelectionStatement) node.jjtGetChild(0);
			if(selNode.getImage().equals("switch"))
				return false;
			ASTStatement ifClause = (ASTStatement) selNode.jjtGetChild(1);
			int n = ifClause.findChildrenOfType(ASTJumpStatement.class).size();
			if(selNode.jjtGetNumChildren() == 2) {
				if(n == 0)
					return false;
				return true;
			} else if(selNode.jjtGetNumChildren() == 3) {
				ASTStatement elseClause = (ASTStatement) selNode.jjtGetChild(2);
				int m = elseClause.findChildrenOfType(ASTJumpStatement.class).size();
				if(n == 1 && n == m)
					return true;
				return false;
			}
		}
		return false;
	}
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsmInstance = fsm.creatInstance();
		fsmInstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) 		
			fsmInstance.setDesp("case in line " + node.getBeginLine() + "does not end with break or return. Avoid to use this.");
		else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
			fsmInstance.setDesp("在第 "+node.getBeginLine()+" 行的case语句不是由break或return终止。" +
					"如果某个case语句最后的break被省略，在执行完该case语句后，系统会继续执行下一个case语句。为了避免编程者的粗心大意，因此禁止 switch的case语句不是由break终止。");
		list.add(fsmInstance);
	}
}
