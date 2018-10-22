package softtest.rules.gcc.rule;

import java.util.*;

import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.database.c.*;
import softtest.fsmanalysis.c.CAnalysis;

/**
 * @author Maojinyu
 * Blank switch
 * 4.3.1.5 禁止使用空switch语句 
 **/
public class BSStateMachine {
	
	public static List<FSMMachineInstance> createBSStateMachines(SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		String xpath = ".//SelectionStatement[@Image='switch']";
		List<SimpleNode> result = StateMachineUtils.getEvaluationResults(node, xpath);
		
		for(Iterator<SimpleNode> itr = result.iterator(); itr.hasNext();) {
			
			ASTSelectionStatement selNode = (ASTSelectionStatement)itr.next();
			
			if(selNode.jjtGetChild(1) instanceof ASTStatement) {
				ASTStatement clause = (ASTStatement)selNode.jjtGetChild(1);
				
				if(clause.jjtGetNumChildren() == 1&&clause.jjtGetChild(0).jjtGetNumChildren()==0) {						//switch(a);
					
					//if((((SimpleNode)(clause.jjtGetChild(0))).getImage()).equals(";")) {
						//if(isRealBlank(selNode, 1)) {
							addFSM(list, clause, fsm);
							continue;
						//}
					//}
				} else if(clause.jjtGetChild(0) instanceof ASTCompoundStatement) {
					ASTCompoundStatement comClause = (ASTCompoundStatement) clause.jjtGetChild(0);
					if(comClause.jjtGetNumChildren() == 0) {				//switch(a){}
						//if(comClause.getImage().equals("{") && comClause.getSecondImage().equals("}")) {
							//if(isRealBlank(selNode, 2)) {
								addFSM(list, comClause, fsm);
								continue;
							//}
						//}
					} else {												//switch(a){;;;;}
						ASTStatementList stalist = (ASTStatementList)comClause.jjtGetChild(0);
						ASTStatement firstClause = (ASTStatement)stalist.jjtGetChild(0);
						if(firstClause.jjtGetChild(0).jjtGetNumChildren() == 0 ) {
							//if(isRealBlank(selNode, 3)) {
								addFSM(list, firstClause, fsm);
								continue;
							//}
						}
					}
				}
			}
		}
		return list;
	}
/**	
	private static boolean isRealBlank(SimpleNode selNode, int condition) {
		String interFilePath = CAnalysis.getCurAnalyElmt().getInterFileName();
		String sourceCode = DBAccess.getSouceCode(interFilePath, selNode.getFileBeginLine(), selNode.getFileEndLine());	
		sourceCode = sourceCode.replaceAll("\\s", "");		//去掉所有空白字符
		String[] temp = sourceCode.split("switch", 2);
		if(temp.length == 2)
			sourceCode = temp[1];							//取得switch后面的代码
		else
			sourceCode = temp[0];
		switch(condition) {
		case 1:
			int count = 1;
			int index = 0;
			for(int i = sourceCode.indexOf("(") + 1; i < sourceCode.length(); i++) {
				if(sourceCode.charAt(i) == '(')
					count++;
				if(sourceCode.charAt(i) == ')')
					count--;
				if(count == 0) {
					index = i;
					break;
				}
			}
			if(index <= sourceCode.length() - 2 && sourceCode.charAt(index + 1) == ';')
				return true;
			else
				return false;
		case 3:
			sourceCode = sourceCode.replaceAll(";", "");		//把case3归结为case2
		case 2:
			if(sourceCode.indexOf("{") == sourceCode.length() - 1)
				return false;
			if(sourceCode.charAt(sourceCode.indexOf("{") + 1) == '}')
				return true;
			else
				return false;
		}	
		return true;
	}*/
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsmInstance = fsm.creatInstance();
		fsmInstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) 		
			fsmInstance.setDesp("There is a blank switch in line " + node.getBeginLine() +". A blank switch doesn't " +
					"have any concrete contents, so don't use it.");
		else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
			fsmInstance.setDesp("在第 "+node.getBeginLine()+" 行出现了空的switch语句。" +
					"空switch语句不具备任何实际的操作内容，因此禁止使用空switch语句。");
		list.add(fsmInstance);
	}
}
