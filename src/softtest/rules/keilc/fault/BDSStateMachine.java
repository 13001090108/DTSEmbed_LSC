package softtest.rules.keilc.fault;


import java.util.LinkedList;
import java.util.List;


import softtest.ast.c.*;
import softtest.ast.c.SimpleNode;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;



/**
 * @author dn
 * Break Dead Statement[break之后的死代码]
 * */
public class BDSStateMachine {
	
	/**
	 * 找到break之后的冗余语句
	 * */
	private static List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
	private static List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
	
	public static List<FSMMachineInstance> createBDSStateMachines(SimpleNode node, FSMMachine fsm){	
		String xpath =".//Statement[./JumpStatement[@Image='break']]";
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		for (SimpleNode snode : evaluationResults) {
			if(snode.jjtGetParent() instanceof ASTLabeledStatement)
				snode = (SimpleNode) snode.jjtGetParent().jjtGetParent();
			
			//找到了当前snode节点，然后find是否该节点后有兄弟节点，如果有，而且是labeled_statement类型,不能加入到list中
			SimpleNode next = findNextStatement((ASTStatement)snode);
			if(next == null || next.jjtGetNumChildren() < 1)
				continue;
			SimpleNode child = (SimpleNode) next.jjtGetChild(0);
			if(child instanceof ASTLabeledStatement && (child.getImage().equals("case") || child.getImage().equals("default"))) {
				continue;
			} else {
				addFSMDesp(child, fsm);
			}
		}
	    return list;
	}
	

	/**
	 * Find the statement after this return statement
	 */
	private static SimpleNode findNextStatement(ASTStatement node) {
		SimpleNode parent = (SimpleNode) node.jjtGetParent();
		if(!(parent instanceof ASTStatementList))
			return null;
		int index = 0;
		for(index=0; index<parent.jjtGetNumChildren(); index++) {
			if(parent.jjtGetChild(index) == node) {
				break;
			}
		}
		index++;
		if(index<parent.jjtGetNumChildren()) {
			SimpleNode next = (SimpleNode) parent.jjtGetChild(index);
			return next;
		}
		return null;
	}


	private static void addFSMDesp(SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		fsminstance.setDesp(" 第" + node.getBeginLine() + "行语句为break语句后的冗余语句，即死码。");
		list.add(fsminstance);
	}
	
}
