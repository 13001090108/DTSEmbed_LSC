package softtest.rules.gcc.question;
import java.util.*;

import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;

/*
 * @author lrt
 * CCI: constant condition if if语句中的常量条件
 *  常量条件即不含有变量 若含有变量,
 */
public class CCIStateMachine {

	public static List<FSMMachineInstance> createCCIStateMachines(SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
		String xpath1 = ".//SelectionStatement[@Image='if']/Expression";
		String xpath2= ".//UnaryExpression/PostfixExpression/PrimaryExpression";
		evaluationResults = StateMachineUtils.getEvaluationResults(node,xpath1);
		Iterator<SimpleNode> itr = evaluationResults.iterator(); //保存了所有if语句中的条件表达式
	    boolean findVariable;
	    ASTAssignmentExpression assignExp=null;
		while(itr.hasNext()){	
			//从当前的expression 找子孙深度为0的primaryexpression,若找不到，则报错 “常量条件”
			SimpleNode snode = (SimpleNode) itr.next();
			List<SimpleNode> peResults = new LinkedList<SimpleNode>();
			peResults = StateMachineUtils.getEvaluationResults(snode,xpath2); //找到所有的primaryexpression
			findVariable = false;
			for(SimpleNode sn: peResults)
			{
				if(sn.getDescendantDepth()==1)
					continue;
				else
				{
					assignExp=null;
					findVariable =true;
					assignExp=(ASTAssignmentExpression)sn.getFirstParentOfType(ASTAssignmentExpression.class);
					 if(assignExp!=null && assignExp.getFirstChildOfType(ASTAssignmentOperator.class)!=null && assignExp.jjtGetParent().jjtGetParent() instanceof ASTSelectionStatement)
						 findVariable=false;
					 else
					 {
						 ASTAssignmentExpression pAssignExp = (ASTAssignmentExpression)assignExp.getFirstParentOfType(ASTAssignmentExpression.class);
						 if(pAssignExp!=null && pAssignExp.getFirstChildOfType(ASTAssignmentOperator.class)!=null && pAssignExp.jjtGetParent().jjtGetParent() instanceof ASTSelectionStatement)
							 findVariable = false;
					 }
					if(findVariable)
						break;
				}
			}
			
			if(!findVariable)//ao!=null  虽然找到了变量 但是变量为赋值表达式
			  addFSM(list,snode,fsm);
			
		}	
	    return list;
	}
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsmInstance = fsm.creatInstance();
		fsmInstance.setRelatedASTNode(node);
		
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) 		
			fsmInstance.setDesp("Warning: Line" + fsmInstance.getRelatedASTNode().getBeginLine()+" Constant condition");
		else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
			fsmInstance.setDesp("警告：第" + fsmInstance.getRelatedASTNode().getBeginLine()+" 行语句中表达式为常量");
		
		list.add(fsmInstance);
	}
}
