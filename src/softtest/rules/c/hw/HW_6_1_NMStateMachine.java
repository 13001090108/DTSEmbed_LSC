package softtest.rules.c.hw;

import java.util.List;
import java.util.LinkedList;
import java.util.Iterator;
import softtest.ast.c.SimpleNode;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.rules.c.StateMachineUtils;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;

/*
 * @author dongna
 * NoMalloc
 */

public class HW_6_1_NMStateMachine {
	public static List<FSMMachineInstance> createNMStateMachines(SimpleNode node, FSMMachine fsm){
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		String xPath = ".//PrimaryExpression";
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);
		Iterator<SimpleNode> itr = evaluationResults.iterator();
		while(itr.hasNext()){
			ASTPrimaryExpression primaryExp = (ASTPrimaryExpression)itr.next();
			if(primaryExp.getImage() == null){
				continue;
			}

			if(primaryExp.getImage().equals("malloc")){
				if(primaryExp.isMethod() && primaryExp.getMethodDecl()!=null && primaryExp.getMethodDecl().isLib())
					addFSM(list, primaryExp, fsm);
			}
				
		}
		return list;
	}
	
	public static void addFSM(List<FSMMachineInstance> list,SimpleNode node,FSMMachine fsm){
		FSMMachineInstance fsmInstance = fsm.creatInstance();
		fsmInstance.setRelatedASTNode(node);
		fsmInstance.setDesp("注意，第" + node.getBeginLine() + "行中使用分配内存，请避免使用");
		list.add(fsmInstance);
	}
}
