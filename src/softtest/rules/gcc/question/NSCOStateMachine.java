package softtest.rules.gcc.question;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.AbstractExpression;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.Type.CType;



public class NSCOStateMachine {

	
	public static List<FSMMachineInstance> createNoShortCircultOperatorMachines(SimpleNode node, FSMMachine fsm){
		/**查询所有出现&和|的表达式*/
		String xpath = ".//SelectionStatement[@Image='if']/Expression//ANDExpression "+
		"| .//SelectionStatement[@Image='if']/Expression//InclusiveORExpression "+
		"|.//IterationStatement[@Image !='for']/Expression//ANDExpression"+
		"|.//IterationStatement[@Image !='for']/Expression//InclusiveORExpression"+
		"|.//IterationStatement[@Image ='for' and count(*)=4]/Expression[2]//ANDExpression"+
		"|.//IterationStatement[@Image ='for' and count(*)=4]/Expression[2]//InclusiveORExpression"+
		"|.//IterationStatement[@Image ='for' and count(*)<4]/Expression[1]//ANDExpression"+
		"|.//IterationStatement[@Image ='for' and count(*)<4]/Expression[1]//InclusiveORExpression";
//		String xpath = ".//ANDExpression |//InclusiveORExpression";
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();	
		List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();	
		
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		Iterator itr = evaluationResults.iterator();
		while(itr.hasNext()){				
			AbstractExpression idExpression = (AbstractExpression)itr.next();	
			CType  type1 =  ((AbstractExpression)idExpression.jjtGetChild(0)).getType();
			CType  type2 =  ((AbstractExpression)idExpression.jjtGetChild(1)).getType();
			if(type1 == null || type2 == null  )
				continue;
			if("bool".equals(type1.getName())|| "bool".equals(type2.getName()))
				addFSM(list, idExpression, fsm);
		}
	    return list;
	}	
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
			fsminstance.setDesp("Use bit operation in this line reduces the performance of code. Suggest use short circult operaotion instead of it.");
		} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
			fsminstance.setDesp("第"+node.getBeginLine()+"行：逻辑表达式中使用了位运算符，从性能上看用短路运算符更好。");
		}	
		list.add(fsminstance);
	}
}
