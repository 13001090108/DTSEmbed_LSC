package softtest.rules.gcc.question;

import java.util.*;

import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;

/*
 * @author liruitong
 * FA Function Address 操作函数地址
 * 函数地址被意外的被用做逻辑条件或算术逻辑运算的操作数。大多数情况下是想调用这个函数，但是却缺失了圆括号。
 * 使用函数地址而不是调用函数可能导致未知程序行为或内存错误。
 */
public class FAStateMachine {

	public static List<FSMMachineInstance> createFAStateMachines(
			SimpleNode node, FSMMachine fsm) {
		String xpath = ".//Declarator[../CompoundStatement]/DirectDeclarator[@Method='true']"; //找到所有的函数声明
		String xpath1 = null;  //找到所有的函数调用
		String image1 = null;
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
		ASTTranslationUnit  translationUnitNode = (ASTTranslationUnit)node.getFirstParentOfType(ASTTranslationUnit.class);
		if(translationUnitNode==null)
		{
			return list;
		}
		evaluationResults = StateMachineUtils.getEvaluationResults(translationUnitNode, xpath);
		
		for (SimpleNode snode : evaluationResults) {//对于该文件中声明的所有函数
			image1 = snode.getImage(); //获得函数名
			xpath1 = ".//Statement//Expression//UnaryExpression/PostfixExpression[@Image='"  + image1  + "']";
			List<SimpleNode> funcs = StateMachineUtils.getEvaluationResults(translationUnitNode, xpath1);
			//对于该函数的每次调用
			if(funcs.size()>0)
			{			
				Iterator itr = funcs.iterator(); 
				while(itr.hasNext()){	
					AbstractExpression postfixExp =(AbstractExpression)itr.next(); 
			
					if(!postfixExp.getOperators().equals("("))
					{
						addFSM(list,postfixExp,fsm);
					}
					else
						continue;
					}
							
				}
			}
		
	    return list;
	}

	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node,
			FSMMachine fsm) {
		FSMMachineInstance fsmInstance = fsm.creatInstance();
		fsmInstance.setRelatedASTNode(node);
        
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH)
			fsmInstance.setDesp("Warning: Line"
					+ node.getBeginLine()
					+ " used function address "+ node.getImage()+ "(Missed brackets).This might lead to unknown program behavior or memeory error");
		else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
			fsmInstance.setDesp("警告：第"
					+ node.getBeginLine()
					+ " 行操作函数地址（函数" +node.getImage() +"圆括号缺失），这可能导致未知程序行为或内存错误");

		list.add(fsmInstance);
	}
}
