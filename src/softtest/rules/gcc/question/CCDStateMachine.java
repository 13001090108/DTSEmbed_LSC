package softtest.rules.gcc.question;
import java.util.*;

import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;

/*
 * @author lrt
 * CCD: constant condition do    do语句中的常量条件
 *  常量条件即不含有变量 若含有变量
 */
public class CCDStateMachine {

	public static List<FSMMachineInstance> createCCDStateMachines(SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
		String xpath1 = ".//Statement/IterationStatement[@Image='do']";
		String xpath2= ".//UnaryExpression/PostfixExpression/PrimaryExpression";
		evaluationResults = StateMachineUtils.getEvaluationResults(node,xpath1);
		Iterator<SimpleNode> itr = evaluationResults.iterator(); 
	    boolean findVariable;
	    ASTAssignmentExpression assignExp=null;
	    
		while(itr.hasNext()){	
			//从当前的expression 找子孙深度为0的primaryexpression,若找不到，则报错 “常量条件”
			SimpleNode snode = (SimpleNode) itr.next();
			if(snode.jjtGetNumChildren()>=2)
			{
				ASTExpression exp =(ASTExpression)snode.jjtGetChild(1); 
			
			List<SimpleNode> peResults = new LinkedList<SimpleNode>();
			peResults = StateMachineUtils.getEvaluationResults(exp,xpath2); //找到所有的primaryexpression
			findVariable = false;
			for(SimpleNode sn: peResults)
			{
				assignExp=null;
				if(sn.getDescendantDepth()==1)//primaryexpression-> constant
				{
					ASTConstant cons = (ASTConstant)sn.getFirstChildOfType(ASTConstant.class);
					if(cons!=null && cons.getImage().equals("0") ||cons.getImage().equals("1") ) //排除程序中常用的while(0)和while(1)两种情况
					{
						findVariable = true; 
						if(exp.getDescendantDepth()!=5)	
						    findVariable = false; 
					}
				}
				else
				{	
					findVariable = true; 
					assignExp=(ASTAssignmentExpression)sn.getFirstParentOfType(ASTAssignmentExpression.class);
					 if(assignExp!=null && assignExp.getFirstChildOfType(ASTAssignmentOperator.class)!=null && assignExp.jjtGetParent().jjtGetParent() instanceof ASTIterationStatement)
						 findVariable=false;
					 else
					 {
						 ASTAssignmentExpression pAssignExp = (ASTAssignmentExpression)assignExp.getFirstParentOfType(ASTAssignmentExpression.class);
						 if(pAssignExp!=null && pAssignExp.getFirstChildOfType(ASTAssignmentOperator.class)!=null && pAssignExp.jjtGetParent().jjtGetParent() instanceof ASTIterationStatement)
							 findVariable = false;
					 }
				}
				if(findVariable)
					break;
			}
			
			if(!findVariable)//ao!=null  虽然找到了变量 但是变量为赋值表达式
			  addFSM(list,snode,fsm);
			}
		}	
	    return list;
	}
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsmInstance = fsm.creatInstance();
		fsmInstance.setRelatedASTNode(node);
		
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) 		
			fsmInstance.setDesp("Warning: Line" + fsmInstance.getRelatedASTNode().getBeginLine()+" Constant condition");
		else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
			fsmInstance.setDesp("警告：第" + fsmInstance.getRelatedASTNode().getBeginLine()+" 行do语句中while条件表达式为常量");
		
		list.add(fsmInstance);
	}
}
