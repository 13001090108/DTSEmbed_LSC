package softtest.rules.gcc.rule;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;


import softtest.ast.c.*;

import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.Type.*;

/** 
 * @author LiuChang
 * 谨慎对指针进行代数运算 
 *  AlgebraicOperationOnPointer  
 */

public class AOOPStateMachine {

	public static List<FSMMachineInstance> createAOOPStateMachines(SimpleNode node, FSMMachine fsm){
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = null;
		//查找算术运算（加，减，乘，除取余）下的id
		//排除p++，p--等常用算术运算
		String xPath=".//Expression/AssignmentExpression//AdditiveExpression//PostfixExpression | .//Expression/AssignmentExpression//MultiplicativeExpression//PostfixExpression";
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);
		Iterator itr = evaluationResults.iterator();

		while(itr.hasNext()){
			ASTPostfixExpression pm=(ASTPostfixExpression)itr.next();
			
			if(pm.getType() == null)
				continue;
			if(pm.getType() instanceof CType_Pointer)
				addFSM(list,pm,fsm);
		}
			
		return list;
	     
  }

	private static void addFSM(List<FSMMachineInstance> list, ASTPostfixExpression node, FSMMachine fsm) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp("AlgebraicOperationOnPointer: An algebraic operation on pointer may lead to greater danger,so  algebraic operating on pointer should be used carefully.");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("谨慎对指针进行代数运算:对指针进行代数运算是具有较大风险的，应谨慎对指针进行代数运算。");
			}	
		
		list.add(fsminstance);
	}
}


