package softtest.rules.gcc.question;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.ASTArgumentExpressionList;
import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTConstant;
import softtest.ast.c.ASTPostfixExpression;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;


/**
 * author: YX
 * 模式：：打印参数不足(Question:PRINT_FORMAT)
 */

public class FEWStateMachine {
	
	
	public static List<FSMMachineInstance> createFEWStateMachines(SimpleNode node, FSMMachine fsm){
		
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();	
		List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();	
		
		String xpath = ".//PostfixExpression";

		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		Iterator itr = evaluationResults.iterator();
		
		while(itr.hasNext()) {
			
			ASTPostfixExpression astpe = (ASTPostfixExpression)itr.next();
			
			int childNum = astpe.jjtGetNumChildren();
			
			if (childNum == 2) {
				ASTPrimaryExpression pre = (ASTPrimaryExpression)astpe.jjtGetChild(0);
				String preName = pre.getImage();
				
				ASTArgumentExpressionList astel = (ASTArgumentExpressionList)astpe.jjtGetChild(1);
				
				int childN = astel.jjtGetNumChildren();
				
				if ("sprintf".equals(preName) || "fprintf".equals(preName)) {

					ASTConstant astae = (ASTConstant)astel.getFirstChildOfType(ASTConstant.class);
					String astaeName = astae.getImage();
					
					int num = getNum(astaeName);
					
					int listNumber = childN - 2;
					
					if (num > listNumber)
						addFSM(list, astpe, fsm);					
				}
				
				if ("snprintf".equals(preName)) {

					ASTConstant astae = (ASTConstant)astel.getFirstChildOfType(ASTConstant.class);
					String astaeName = astae.getImage();
					
					int num = getNum(astaeName);
					
					int listNumber = childN - 3;
					
					if (num > listNumber)
						addFSM(list, astpe, fsm);
				}
				
				if ("printf".equals(preName)) {

					ASTConstant astae = (ASTConstant)astel.getFirstChildOfType(ASTConstant.class);
					String astaeName = astae.getImage();
					
					int num = getNum(astaeName);
					
					int listNumber = childN - 1;
					
					if (num > listNumber)
						addFSM(list, astpe, fsm);
				}
			}			
		}
	    return list;
	}	
	
	public static int getNum(String all) {
		int total = 0;
		char array[] = all.toCharArray();
		
		for (int i=0; i<array.length; ++i) {			
			if ('%' == array[i]) {
				total++;
				i++;
			}
		}
		return total;
	}
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
			fsminstance.setDesp("Print too few parameters.");
		} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
			fsminstance.setDesp("打印参数不足。");
		}	
		list.add(fsminstance);
	}
}