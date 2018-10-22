package softtest.rules.gcc.question;

import java.util.Iterator;
/**
 * @author yx
 * 修正类型不匹配
 */
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

public class PFMStateMachine {
	
	public static List<FSMMachineInstance> createPFMStateMachines(SimpleNode node, FSMMachine fsm){
		
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
					
					boolean flag = unknown(astaeName);
					if (!flag)
					    addFSM(list, astpe, fsm);					
				}
				
				if ("snprintf".equals(preName)) {
					
					ASTConstant astae = (ASTConstant)astel.getFirstChildOfType(ASTConstant.class);
					String astaeName = astae.getImage();
					
					boolean flag = unknown(astaeName);
					if (!flag)
						addFSM(list, astpe, fsm);				
				}
				
				if ("printf".equals(preName)) {
					
					ASTConstant astae = (ASTConstant)astel.getFirstChildOfType(ASTConstant.class);
					String astaeName = astae.getImage();
					
					boolean flag = unknown(astaeName);
					if (!flag)
						addFSM(list, astpe, fsm);	
				}
			}			
		}
		return list;
	}
		
	private static boolean unknown(String all) {
		
		String result[] = all.split("%");
		
		boolean flag = false;
		for (int i = 0; i < result.length; ++i) {
			char a[] = result[i].toCharArray();
						
			for (int j = 0; j < a.length; ++j) {
				if (a[j] == '"')
					continue;
				
				if (Character.isLetter(a[j])){
					if ((a[j] == 'h') && (a[j+1] =='h')) {
						if (!match1(a[j+2])) {
							flag = true;
							   break;
						}
					} else if ((a[j] == 'l') && (a[j+1] == 'l')) {
						if (!match2(a[j+2])) {
							flag = true;
							   break;
						}
					} else if (a[j]=='h') {
						if (!match1(a[j+1])) {
							flag = true;
							   break;
						}		
					} else if (a[j]=='l' || a[j]=='t' ||a[j]=='z') {
						if (!match2(a[j+1])) {
							flag = true;
							   break;
						}						
					} 
					if (a[j] == 'L') {
						if (!match3(a[j+1])) {
							flag = true;
							break;
						}						
					}
					break;
				}
			}			
		}
		if (flag == true) 
			return false;
		return true;
	}
	
	private static boolean match1(char c) {
		
		if (c == 'u' || c == 'd' || c == 'x' || c == 'i' ||c =='X' || c =='o')
		    return true;
		
		return false;		
	}
	
	private static boolean match2(char c) {
		
		if (c == 'u' || c == 'd' || c == 'x' || c == 'i' ||c =='X' || c =='o' || c == 'c')
		    return true;
		
		return false;
	}
	
	private static boolean match3(char c) {
		if (c == 'a' || c == 'A' || c == 'e' || c == 'E' ||c =='f' || c =='g' || c =='G')
		    return true;
		
		return false;	
	}
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
			fsminstance.setDesp("Correction type does not match.");
		} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
			fsminstance.setDesp("修正类型不匹配。");
		}	
		list.add(fsminstance);
	}
}
