package softtest.rules.c.fault;

import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTDirectDeclarator;
import softtest.ast.c.ASTInitDeclarator;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.VexNode;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.symbolic.Expression;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.DefUseAnalysis.c.LiveDefsSet;;

/**
 * @author st
 * LUN - intLock intUnlock Not match 
 * 此模式仅针对intLock和intUnlock不嵌套的情况
 */
public class LUNStateMachine {
	
	private enum ErrorType {
		LOCK_UNLOCK,
		LOCK_ONLY,
		UNLOCK_ONLY,
	}
	
	public static List<FSMMachineInstance> createLUNStateMachines(SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		String lockXpath = ".//Declaration/InitDeclaratorList/InitDeclarator[count(*)=2][/Initializer/AssignmentExpression[@Image='intLock']]|" +
						   ".//AssignmentExpression[count(*)=3][/AssignmentOperator[@Operators='=']][/AssignmentExpression[@Image='intLock']]";
		String unlockXpath = ".//AssignmentExpression[@Image='intUnlock']/UnaryExpression/PostfixExpression/ArgumentExpressionList/AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression";
		List<SimpleNode> lockNodes = StateMachineUtils.getEvaluationResults(node, lockXpath);
		List<SimpleNode> unlockNodes = StateMachineUtils.getEvaluationResults(node, unlockXpath);

		if(lockNodes.size() != 0 && unlockNodes.size() != 0) {
			for(SimpleNode snode : lockNodes) {
				addFSM(list,snode, fsm, ErrorType.LOCK_UNLOCK);
			}
		} else if(lockNodes.size() != 0 && unlockNodes.size() == 0) {
			addFSM(list, lockNodes.get(0), fsm, ErrorType.LOCK_ONLY);
		} else if(lockNodes.size() == 0 && unlockNodes.size() != 0) {
			addFSM(list, unlockNodes.get(0), fsm, ErrorType.UNLOCK_ONLY);
		}
		return list;
	}
	
	public static boolean checkLock(VexNode vex, FSMMachineInstance fsmin) {
		if(vex == fsmin.getReleatedVexNode() && fsmin.getStateData() != null
				&& fsmin.getStateData() instanceof Set) {
			return true;
		}
		return false;
	}
	
	public static boolean checkError(VexNode vex, FSMMachineInstance fsmin) {
		if(vex == fsmin.getReleatedVexNode() && fsmin.getStateData() != null
				&& ( fsmin.getStateData() == ErrorType.LOCK_ONLY || fsmin.getStateData() == ErrorType.UNLOCK_ONLY ) ) {
			return true;
		}
		return false;
	}
	
	public static boolean checkNotMatch(List nodes, FSMMachineInstance fsmin) {
		boolean match = isMatch(nodes, fsmin);
		if(!match) {
			fsmin.setDesp(fsmin.getDesp() + "第" + ((SimpleNode)nodes.get(0)).getBeginLine() + "行的intUnlock允许中断与之不匹配");
		}
		return !match;
	}
	
	public static boolean checkMatch(List nodes, FSMMachineInstance fsmin) {
		for(Iterator itr = nodes.iterator(); itr.hasNext();) {
			SimpleNode node = (SimpleNode) itr.next();
			VariableNameDeclaration varDecl = node.getVariableNameDeclaration();
			Set alias = (Set) fsmin.getStateData();
			if(alias.contains(varDecl)) {
				return true;
			}
		}
		return false;
	}
	
	private static boolean isMatch(List nodes, FSMMachineInstance fsmin) {
		for(Iterator itr = nodes.iterator(); itr.hasNext();) {
			SimpleNode node = (SimpleNode) itr.next();
			VariableNameDeclaration varDecl = node.getVariableNameDeclaration();
			Set alias = (Set) fsmin.getStateData();
			if(alias.contains(varDecl)) {				
				SimpleNode node_fsm = fsmin.getRelatedASTNode();
				VexNode v = node.getCurrentVexNode();
				VexNode v_fsm = node_fsm.getCurrentVexNode();
				
				Hashtable<VariableNameDeclaration, Expression> vTable=v.getValueSet().getTable();
				Hashtable<VariableNameDeclaration, Expression> vTable_fsm=v_fsm.getValueSet().getTable();
				Expression e = vTable.get(varDecl);
				Expression e_fsm = vTable_fsm.get(varDecl);
				String s = e.toString();
				String s_fsm = e_fsm.toString();
				if(s.equals(s_fsm)){
					return true;
				}else{
					return false;
				}				
			}			
		}
		return false;
	}
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm, ErrorType condition) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		fsminstance.setReleatedVexNode(node.getCurrentVexNode());
		VariableNameDeclaration varDecl = null;
		switch(condition) {
		case LOCK_UNLOCK:
			Set<VariableNameDeclaration> alias = new HashSet<VariableNameDeclaration>();
			if(node instanceof ASTInitDeclarator) {
				List dels = node.findChildrenOfType(ASTDirectDeclarator.class);
				if(dels.size() != 0) {
					ASTDirectDeclarator del = (ASTDirectDeclarator) dels.get(0);
					varDecl = del.getVariableNameDeclaration();
				}
			} else if(node instanceof ASTAssignmentExpression) {
				ASTPrimaryExpression primaryNode = DMStateMachine.getPrimarynode(node);//得到等号左边的变量
				varDecl = primaryNode.getVariableDecl();
			}
			if(varDecl != null) {
				alias.add(varDecl);
				fsminstance.setStateData(alias);
				fsminstance.setDesp("在第" + node.getBeginLine() + "行使用intLock禁止中断,");
			}
			break;
		case LOCK_ONLY:
			fsminstance.setStateData(ErrorType.LOCK_ONLY);
			fsminstance.setDesp("在第" + node.getBeginLine() + "行使用intLock禁止中断，之后并没有相应的intUnlock允许中断");
			break;
		case UNLOCK_ONLY:
			fsminstance.setStateData(ErrorType.UNLOCK_ONLY);
			fsminstance.setDesp("在第" + node.getBeginLine() + "行使用intUnlock允许中断，之前并没有相应的intLock禁止中断");
			break;
		}
		list.add(fsminstance);
	} 
}
