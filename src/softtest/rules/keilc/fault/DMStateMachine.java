package softtest.rules.keilc.fault;

import static org.junit.Assert.fail;

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.jaxen.JaxenException;

import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTAssignmentOperator;
import softtest.ast.c.ASTMultiplicativeExpression;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTConstant;
import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.ParseException;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.VexNode;
import softtest.domain.c.symbolic.Expression;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.NameOccurrence;
import softtest.symboltable.c.Scope;
import softtest.symboltable.c.VariableNameDeclaration;

/**
 * @author st
 * DM - Duplicate Mod 
 * */

public class DMStateMachine {
	
	public static List<FSMMachineInstance> createDMStateMachines(SimpleNode node, FSMMachine fsm) {
		
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		String xpath = ".//AssignmentExpression[/AssignmentOperator[@Operators='=']][/AssignmentExpression/MultiplicativeExpression[@Operators='%']]|" +
					".//AssignmentExpression[/AssignmentOperator[@Operators='%=']]"; 
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		// 为每个取模运算的变量创建状态机实例(a = a % xx; a %= xx;)
		for(Iterator<SimpleNode> itr = evaluationResults.iterator(); itr.hasNext(); ) {
			SimpleNode assignNode = itr.next();
			ASTPrimaryExpression primaryNode = getPrimarynode(assignNode);
			if(primaryNode == null) {
				continue;
			}
			VariableNameDeclaration varDecl = primaryNode.getVariableDecl();
			if(varDecl == null) {
				continue;
			}
			ASTAssignmentOperator operator = null;
			if(assignNode.jjtGetChild(1) instanceof ASTAssignmentOperator) {
				operator = (ASTAssignmentOperator) assignNode.jjtGetChild(1);
			}
			if(operator.getOperatorType() != null) {
				if(operator.getOperatorType().toString().equals("[=]")) {
					if(assignNode.jjtGetChild(2) instanceof ASTAssignmentExpression) {
						ASTMultiplicativeExpression multipleNode = (ASTMultiplicativeExpression) assignNode.jjtGetChild(2).jjtGetChild(0);
						ASTPrimaryExpression primaryNodeRight = getPrimarynode(multipleNode);
						if(primaryNodeRight == null) {
							continue;
						}
						VariableNameDeclaration varDeclRight = primaryNodeRight.getVariableDecl();
						if(varDeclRight == varDecl) {
							addFSM(list, primaryNode, fsm);
						}
					}
				} else if(operator.getOperatorType().toString().equals("[%=]")) {
						addFSM(list, primaryNode, fsm);
				}
			}
		}
		return list;
	}
	
	public static boolean checkSameVarMod(List nodes, FSMMachineInstance fsmin) {
		for(Iterator itr = nodes.iterator(); itr.hasNext();) {
			ASTAssignmentExpression assignNode = (ASTAssignmentExpression) itr.next();
			ASTPrimaryExpression primaryNode = getPrimarynode(assignNode);
			if(primaryNode != null && primaryNode == fsmin.getRelatedASTNode() && assignNode.getCurrentVexNode() == fsmin.getReleatedVexNode()) {
				return true;
			}
		}
		return false;
	}
	/**
	 * @author Liuli
	 *2010-4-21
	 */
	public static boolean checkAssign(SimpleNode node, FSMMachineInstance fsmin) {
		ASTPrimaryExpression primaryNode = getPrimarynode(node);
		VariableNameDeclaration varDecl = primaryNode.getVariableDecl();
		ASTAssignmentExpression parent = (ASTAssignmentExpression)fsmin.getRelatedASTNode().jjtGetParent().jjtGetParent().jjtGetParent();
		ASTAssignmentOperator operator_fsm = (ASTAssignmentOperator) parent.jjtGetChild(1);
		
		ASTPrimaryExpression test = null;
		ASTConstant c = null,c1 = null , c2 = null;
		SimpleNode node_fsm = fsmin.getRelatedASTNode();
		VexNode v = node.getCurrentVexNode();
		VexNode v_fsm = node_fsm.getCurrentVexNode();
		Hashtable<VariableNameDeclaration, Expression> vTable=v.getValueSet().getTable();
		Hashtable<VariableNameDeclaration, Expression> vTable_fsm=v_fsm.getValueSet().getTable();
		
		String s = null;
		String s_fsm = null;
				
		if(operator_fsm.getOperators().equals("=")){
			test = (ASTPrimaryExpression) parent.jjtGetChild(2).jjtGetChild(0).jjtGetChild(1).jjtGetChild(0).jjtGetChild(0);
			if(test.jjtGetNumChildren() != 0){//为常数情况
				if(!( test.jjtGetChild(0)instanceof ASTConstant))//只处理除数为常数或变量的情况，表达式不考虑
					return true;
				c = (ASTConstant) test.jjtGetChild(0);
				s_fsm = c.getImage();
			}else{//变量情况
				VariableNameDeclaration varDecl1 = test.getVariableDecl();
				Expression e = vTable_fsm.get(varDecl1);
				s_fsm = e.toString();
			}
		}
		if(operator_fsm.getOperators().equals("%=")){
			test = (ASTPrimaryExpression) parent.jjtGetChild(2).jjtGetChild(0).jjtGetChild(0).jjtGetChild(0);
			if(test.jjtGetNumChildren() != 0){
				if(!( test.jjtGetChild(0)instanceof ASTConstant))
					return true;
				c = (ASTConstant) test.jjtGetChild(0);
				s_fsm = c.getImage();
			}else{
				VariableNameDeclaration varDecl1 = test.getVariableDecl();
				Expression e = vTable_fsm.get(varDecl1);
				s_fsm = e.toString();
			}
		}
		
		if (varDecl != null && varDecl == fsmin.getRelatedVariable()) {
			if (node.jjtGetNumChildren() == 3 && node.jjtGetChild(1) instanceof ASTAssignmentOperator) {
				ASTAssignmentOperator operator = (ASTAssignmentOperator) node.jjtGetChild(1);
				
				if(operator.getOperators().equals("%=")){//只需判断除数是否相同			
					ASTPrimaryExpression test1 = (ASTPrimaryExpression)node.jjtGetChild(2).jjtGetChild(0).jjtGetChild(0).jjtGetChild(0);
					if(test1.jjtGetNumChildren() != 0){
						if(!( test1.jjtGetChild(0)instanceof ASTConstant))
							return true;
						c1 = (ASTConstant) test1.jjtGetChild(0);
						s = c1.getImage();
					}else{
						VariableNameDeclaration varDecl1 = test1.getVariableDecl();
						Expression e = vTable.get(varDecl1);
						s = e.toString();
					}
											
					if (!s_fsm.equals(s)) {
						return true;
					}else{
						return false;
					}
				}
								
				if (operator.getOperators().equals("=")) { 
					SimpleNode assignNode = (SimpleNode) node.jjtGetChild(2);
					if (assignNode.jjtGetNumChildren() == 1
							&& assignNode.jjtGetChild(0) instanceof ASTMultiplicativeExpression) {
						ASTMultiplicativeExpression multipleNode = (ASTMultiplicativeExpression) assignNode.jjtGetChild(0);
						if (multipleNode.getOperators().equals("%")) {
							ASTPrimaryExpression primaryNode2 = getPrimarynode(multipleNode);
							if (primaryNode2 != null) {
								VariableNameDeclaration varDecl2 = primaryNode2.getVariableDecl();
								if (varDecl2 != null && varDecl2 != varDecl) {
									return true;
								} else {									
									ASTPrimaryExpression test2 = (ASTPrimaryExpression) assignNode
											.jjtGetChild(0).jjtGetChild(1)
											.jjtGetChild(0).jjtGetChild(0);	
									if(test2.jjtGetNumChildren() != 0){
										if(!( test2.jjtGetChild(0)instanceof ASTConstant))
											return true;
										c2 = (ASTConstant) test2.jjtGetChild(0);
										s = c2.getImage();
									}else{
										VariableNameDeclaration varDecl1 = test2.getVariableDecl();
										Expression e = vTable.get(varDecl1);
										s = e.toString();
									}

									if (!s_fsm.equals(s)) {
										return true;
									}
								}
							} else {
								return true;
							}
						} else {
							return true;
						}
					}
				}
			}
		} else {
			return true;
		}
		return false;
	}
	
	public static boolean checkDuplicateMod(List nodes, FSMMachineInstance fsmin) {
		for(Iterator itr = nodes.iterator(); itr.hasNext();) {
			SimpleNode node = (SimpleNode) itr.next();
			ASTPrimaryExpression primaryNode = getPrimarynode(node);
			if(primaryNode != null && primaryNode != fsmin.getRelatedASTNode() && node.getCurrentVexNode() != fsmin.getReleatedVexNode()) {
				VariableNameDeclaration varDecl = primaryNode.getVariableDecl();
				//liuli 2010.4.20
				if(varDecl != null && !checkAssign(node,fsmin)) {
					if(checkAssignedAgain(node,fsmin.getRelatedASTNode(),varDecl)){//查看是否被重定义过
						return false;
					}
					fsmin.setDesp(fsmin.getDesp() + "在第" + node.getBeginLine() + "行再次进行了没有意义的取模运算");
					return true;
				}
			}
		}
		return false;
	}
	
	private static int num=1;
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		VariableNameDeclaration varDecl = ((ASTPrimaryExpression)node).getVariableDecl();
		fsminstance.setRelatedASTNode(node);
		fsminstance.setRelatedVariable(varDecl);
		fsminstance.setReleatedVexNode(node.getCurrentVexNode());
		fsminstance.setDesp("变量" + varDecl.getImage() + "在第" + node.getBeginLine() + "行进行了取模运算，");
		list.add(fsminstance);
	}
	
	public static ASTPrimaryExpression getPrimarynode(SimpleNode node) {
		List primaryNodes = null;
		try {
			primaryNodes = node.findChildNodesWithXPath("./UnaryExpression[1]/PostfixExpression/PrimaryExpression[count(*)=0]");
		} catch (JaxenException e) {
			e.printStackTrace();
		}
		if(primaryNodes != null && primaryNodes.size() != 0) {
			return (ASTPrimaryExpression) primaryNodes.get(0);
		}
		return null;
	}
	/**
	 * @author Liuli
	 *2010-4-21
	 */
	private static boolean checkAssignedAgain(SimpleNode node,SimpleNode node_fsm, VariableNameDeclaration variable) {
		Scope scope = variable.getScope();
		Map<VariableNameDeclaration, ArrayList<NameOccurrence>> varOccs = scope.getVariableDeclarations();

		List<NameOccurrence> occs = varOccs.get(variable);
		List<NameOccurrence> list = new LinkedList<NameOccurrence>();//定义取消链
		
		if(occs==null)
			return false;
		if(node.getBeginLine()<node_fsm.getBeginLine()){
			for(NameOccurrence occ : occs){
				if(occ.getLocation() == node) {
					list = occ.getDef_undef();
					if(list==null){  						
						break;
					}else{
						for(int i = 0;i<list.size();i++){
							if(list.get(i).getLocation().getBeginLine() < node_fsm.getBeginLine() && list.get(i).getLocation().getBeginLine()>node.getBeginLine())
								return true;	
						}
					}
				}
			}
		}
		if(node.getBeginLine()>node_fsm.getBeginLine()){
			for(NameOccurrence occ : occs){
				if(occ.getLocation() == node_fsm) {
					list = occ.getDef_undef();
					if(list==null){  						
						break;
					}else{
						for(int i = 0;i<list.size();i++){
							if(list.get(i).getLocation().getBeginLine() > node_fsm.getBeginLine() && list.get(i).getLocation().getBeginLine()<node.getBeginLine())
								return true;	
						}
					}
				}
			}
		}		
		return false;	
	}
}
