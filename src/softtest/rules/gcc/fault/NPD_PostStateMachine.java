package softtest.rules.gcc.fault;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;

import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.VexNode;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.DomainType;
import softtest.domain.c.interval.IntegerDomain;
import softtest.domain.c.interval.PointerDomain;
import softtest.domain.c.interval.PointerValue;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.interpro.c.Variable;
import softtest.rules.c.BasicStateMachine;
import softtest.rules.c.StateMachineUtils;
import softtest.summary.c.MethodFeature;
import softtest.summary.c.MethodPostCondition;
import softtest.summary.c.MethodSummary;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.Type.CType_Pointer;

/**
 * 函数后置信息引起的空指针引用  
 * @author cjie
 */
public class NPD_PostStateMachine extends BasicStateMachine {
	@Override
	public void registFetureVisitors() {
		super.registFetureVisitors();
		//InterContext.addPreConditionVisitor(MethodUFMPreConditionVisitor.getInstance());
	}
	public static List<FSMMachineInstance> createNPD_PostStateMachines(SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new ArrayList<FSMMachineInstance>();
		String xpath = ".//PrimaryExpression[@Method='true']";
		List<SimpleNode> nodes = StateMachineUtils.getEvaluationResults(node, xpath);
		for(SimpleNode snode : nodes) {
			MethodNameDeclaration methodDecl = null;
			if(snode instanceof ASTPrimaryExpression) {
				methodDecl = (MethodNameDeclaration) ((ASTPrimaryExpression)snode).getMethodDecl();
			}
//			else {
//				methodDecl = (MethodNameDeclaration) ((ASTqualified_id)snode).getNameDeclaration();
//			}
			if(methodDecl == null || methodDecl.isLib()) {
				continue;
			}
			MethodSummary mtSummary = methodDecl.getMethodSummary();
			if(mtSummary == null) {
				continue;
			}

			for(MethodFeature feature : mtSummary.getPostConditions()) {
				if(feature instanceof MethodPostCondition) {
					MethodPostCondition post = (MethodPostCondition) feature;
					for(Entry<Variable, Domain> entry : post.getPostConds().entrySet()) {
						if(entry.getKey().getType() instanceof CType_Pointer) {
							Domain domain = entry.getValue();
							if(domain instanceof PointerDomain) {
								PointerDomain pDomain = (PointerDomain) domain;
								if(pDomain.getValue() == PointerValue.NULL ||pDomain.getValue() == PointerValue.NULL_OR_NOTNULL) {
									addFSM(list, snode, entry.getKey(), fsm);
								}
							} else if(domain instanceof IntegerDomain) {
								IntegerDomain iDomain = (IntegerDomain) domain;
								if(iDomain.contains(0)) {
									addFSM(list, snode, entry.getKey(), fsm);
								}
							}
						}
					}
				}
			}
		}
		return list;
	}

	public static boolean checkSameVex(VexNode vex, FSMMachineInstance fsmin) {
		if(vex == fsmin.getReleatedVexNode()) {
			return true;
		}
		return false;
	}
	
	public static boolean checkNPDPost(List nodes, FSMMachineInstance fsmin) {
		for(Iterator itr = nodes.iterator(); itr.hasNext();) {
			SimpleNode node = (SimpleNode) itr.next();
			VariableNameDeclaration varDecl = node.getVariableNameDeclaration();
			if(varDecl == null) {
				return false;
			}
			VexNode vex = node.getCurrentVexNode();
			Domain domain = vex.getDomain(varDecl);
			if (domain instanceof PointerDomain) {
				PointerDomain pd = (PointerDomain) domain;
				if (pd.getDomaintype() != DomainType.UNKNOWN && (pd.getValue() == PointerValue.NULL || pd.getValue() == PointerValue.NULL_OR_NOTNULL)) {
//					if(pd.AllocType == CType_AllocType.Null && pd.getValue() == PointerValue.NULL && pd.offsetRange != null && !pd.offsetRange.isEmpty()) {
//						return false;
//					}
					if (Variable.getVariable(varDecl) != null) {
						if(Variable.getVariable(varDecl).getName().equals(((Variable) fsmin.getStateData()).getName()) && NPDStateMachine.confirmNPD(node, varDecl)) {
							fsmin.setRelatedASTNode(node);
							fsmin.setRelatedVariable(varDecl);
							fsmin.setDesp(fsmin.getDesp() + "在第" + node.getBeginLine() + "行可能为一个空指针引用");
							return true;
						}
					}
				}
			}

		}
		return false;
	}
	
	public static boolean checkAssign(List nodes, FSMMachineInstance fsmin) {
		for(Iterator itr = nodes.iterator(); itr.hasNext();) {
			SimpleNode node = (SimpleNode) itr.next();
			VariableNameDeclaration varDecl = node.getVariableNameDeclaration();
			if(varDecl == null) {
				return false;
			}
			if(Variable.getVariable(varDecl) == fsmin.getStateData()) {
				return true;
			}
		}
		return false;
	}
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, Variable v, FSMMachine fsm) {
		FSMMachineInstance fsmInstance = fsm.creatInstance();
		fsmInstance.setDesp("变量" + v.getName() + "在第" + node.getBeginLine() + "行的函数调用后可能为空,");
		fsmInstance.setStateData(v);
		fsmInstance.setReleatedVexNode(node.getCurrentVexNode());
		list.add(fsmInstance);
	}
	
}
