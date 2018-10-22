package softtest.rules.gcc.rule;

import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.VariableNameDeclaration;

/** 
* @author xiangwentao
* Forbid Variable Name as l and O
* 禁止单独使用小写字母“1”或大写字母“O”作为变量名(语句使用类)
*/
public class FVNStateMachine {
	
	public static List<FSMMachineInstance> createFVNMachines(SimpleNode node, FSMMachine fsm) {
		
		 List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		//找到所有的id_expression与qualified_id
	    String xPath = ".//Statement//Declaration//DirectDeclarator[@Image='l' or @Image='O']";
	    xPath+="| .//ParameterList//DirectDeclarator[@Image='l' or @Image='O']";
	    
	    List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);
	    VariableNameDeclaration variable = null;
	    for (SimpleNode snode : evaluationResults) {
			variable = snode.getVariableNameDeclaration();
			if(variable == null )
				continue;		
			FSMMachineInstance fsminstance = fsm.creatInstance();
			fsminstance.setRelatedASTNode(node);
			fsminstance.setRelatedVariable(variable);
			addFSMDescription(fsminstance);
			list.add(fsminstance);
		}
	    return list;
	}
	
	private static void addFSMDescription(FSMMachineInstance fsminstance){
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
			fsminstance.setDesp("Forbid using 'l' or 'O' as Variable Name");
		} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
			fsminstance.setDesp("禁止单独使用小写字母“1”或大写字母“O”作为变量名");
		}
	}
	
	
}
