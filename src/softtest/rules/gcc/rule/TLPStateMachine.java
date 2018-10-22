package softtest.rules.gcc.rule;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;


import softtest.ast.c.*;

import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.Type.CType_BaseType;

/** 
 * @author DongNa
 * 禁止指针的指针超过两级
 * ThreeormoreLevelpointer 
 */

public class TLPStateMachine {

	public static List<FSMMachineInstance> createTLPStateMachines(SimpleNode node, FSMMachine fsm){
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = null;
		List<SimpleNode> secondPointer= null;
		
		String xPath=".//Declarator/Pointer";
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);
		Iterator itr = evaluationResults.iterator();
		
		while(itr.hasNext()){
			ASTPointer pointer= (ASTPointer)itr.next();
			if(pointer.findDirectChildOfType(ASTPointer.class).size()!=0){
				//找到二级指针
				secondPointer=pointer.findDirectChildOfType(ASTPointer.class);
				if(secondPointer.get(0).findDirectChildOfType(ASTPointer.class).size()!=0)
					addFSM(list,pointer,fsm);
				}
		}
			
		return list;
	     
  }

	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp(" ThreeormoreLevelpointer: Using pointer of pointer which more than two levels is dangerous."+node.getBeginLine());
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("第"+node.getBeginFileLine()+"行出现指针的指针超过两级: 当指针的指针超过两级时，使用起来具有很大风险。");
			}	
		
		list.add(fsminstance);
	}
}
