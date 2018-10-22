package softtest.rules.gcc.question;


import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.jaxen.JaxenException;

import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.database.c.DBAccess;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.fsmanalysis.c.CAnalysis;
import softtest.rules.c.StateMachineUtils;

/** 
 * @author YangRui
 */

public class NBCLStateMachine {

	public static List<FSMMachineInstance> createNBCLStateMachines(SimpleNode node, FSMMachine fsm) throws JaxenException{
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> results = null;
		
		String xPath=".//SelectionStatement[./Statement/ExpressionStatement[@DescendantDepth='0']] | .//SelectionStatement[./Statement/CompoundStatement[@DescendantDepth='0']]|.//IterationStatement[./Statement/ExpressionStatement[@DescendantDepth='0']]|.//IterationStatement[./Statement/CompoundStatement[@DescendantDepth='0']]" ;
		results = StateMachineUtils.getEvaluationResults(node, xPath);
		Iterator itr = results.iterator();
		while(itr.hasNext()){
			SimpleNode snode = (SimpleNode)itr.next();
			addFSM(list, snode, fsm);
			}	
		return list;    
	}
	
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp("Null Branch Of Condition Loop： There's a null branch in if or while statement ,which may caused by mistaken adding a \";\"");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("条件、循环语句的空分支: 在if,while语句中存在空分支，有可能是由于误写了一个;号造成。");
			}			
		list.add(fsminstance);
	}
}
