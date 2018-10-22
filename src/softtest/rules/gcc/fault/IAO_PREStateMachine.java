package softtest.rules.gcc.fault;

import java.util.*;

import softtest.cfg.c.VexNode;
import softtest.domain.c.analysis.*;
import softtest.ast.c.*;
import softtest.domain.c.interval.*;
import softtest.domain.c.symbolic.Expression;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.Variable;
import softtest.rules.c.*;
import softtest.summary.gcc.fault.IAOType;
import softtest.summary.gcc.fault.MethodIAOPreCondition;
import softtest.summary.gcc.fault.MethodIAOPreConditionVisitor;
import softtest.summary.gcc.fault.MethodIAOPreCondition.IAOInfo;
import softtest.symboltable.c.*;

public class IAO_PREStateMachine extends BasicStateMachine {

	@Override
	public void registFetureVisitors() {
		super.registFetureVisitors();
		InterContext.addPreConditionVisitor(MethodIAOPreConditionVisitor.getInstance());
	}
	static int i=1;
	public static List<FSMMachineInstance> createIAOStateMachines(SimpleNode node, FSMMachine fsm) {	
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		//找到所有的函数调用节点
		String xPath = ".//PrimaryExpression[@Method='true']";
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);
		
		for (SimpleNode snode : evaluationResults) {
			MethodNameDeclaration methodDecl = StateMachineUtils.getMethodNameDeclaration(snode);
			if(methodDecl == null || methodDecl.getMethodSummary() == null)
				continue;	
			//如果该函数有关于非法计算的前置信息
			MethodIAOPreCondition feature = (MethodIAOPreCondition)methodDecl.getMethodSummary().findMethodFeature(MethodIAOPreCondition.class);
			if (feature == null) {
				continue;
			}
			Set<Variable> variables = feature.getIAOVariables();
			ExpressionValueVisitor expvst = new ExpressionValueVisitor();

			//step1:如果函数的前置信息包含的是对参变量的约束
			for(Variable var : variables) {
				IAOInfo iaoInfo = feature.getIAOInfo(var);
				if(var.isParam()) { 
					SimpleNode param = null;
					if(snode instanceof ASTPrimaryExpression) {
						param = StateMachineUtils.getArgument(snode, var.getParamIndex());
					}
					else {
						//异常处理优先考虑
						SimpleNode decl = (SimpleNode) snode.getFirstParentOfType(ASTDeclaration.class);
						param = (SimpleNode) decl.jjtGetChild(1);
					}
					if(param == null) {
						System.out.println("Func is " + snode.getImage() + " Index is : " +var.getParamIndex() );
						continue;
					}
					ExpressionVistorData visitdata = new ExpressionVistorData();
					visitdata.currentvex = param.getCurrentVexNode();
					visitdata.currentvex.setfsmCompute(true);
					expvst.visit(param, visitdata);
					visitdata.currentvex.setfsmCompute(false);
					Expression value1 = visitdata.value;
					Domain mydomain=null;
					if(value1!=null)
					mydomain = value1.getDomain(visitdata.currentvex.getSymDomainset());
					if(mydomain == null)
						continue;
					//如果myDomain符合iaoInfo，那么添加一个fsmInstance
					if(isContain(mydomain, iaoInfo)) {
						FSMMachineInstance fsminstance = fsm.creatInstance();
//						System.out.println("《测试IAO_PRE》这是产生的第"+i+"个IAO_PRE状态机实例，在第 "+ snode.getBeginLine()+ "行，第"+snode.getBeginColumn()+"列满足状态机产生条件 ");
//						i++;
						addFSMDescript(fsminstance, snode, fsm, iaoInfo, list);
					}
				}
			}
			
			//step2:如果函数的前置信息包含的是对全局变量、成员变量的约束
			if(snode.getCurrentVexNode() == null)
				continue;
			//获得该函数调用之前的变量域集合
			VexNode vexNode=snode.getCurrentVexNode();
			if(vexNode == null)
				continue;
			for(Variable var : variables) {
				IAOInfo iaoInfo = feature.getIAOInfo(var);
				if(!var.isParam()) { //不是参变量，就是全局变量和成员变量
					VariableNameDeclaration varDecl = findLocalVariableDecl(var, node);
					if(varDecl == null)
						continue;
					Domain domain = vexNode.getDomain(varDecl);
					if(domain == null)
						continue;
					if(isContain(domain, iaoInfo)) {
						FSMMachineInstance fsminstance = fsm.creatInstance();
//						System.out.println("《测试IAO_PRE》这是产生的第"+i+"个IAO_PRE状态机实例，在第 "+ snode.getBeginLine() + "行，第"+snode.getBeginColumn()+"列满足状态机产生条件 ");
//						i++;
						addFSMDescript(fsminstance, snode, fsm, iaoInfo, list);
					}
				}
			}
		}
		return list;
	}
	
	public static VariableNameDeclaration findLocalVariableDecl(Variable variable, SimpleNode node) {
		Scope scope = node.getScope().getEnclosingClassScope();
		if (scope == null) {
			scope = node.getScope().getEnclosingSourceFileScope();
		}
		if (scope != null) {
			Set<VariableNameDeclaration> vars = scope.getVariableDeclarations().keySet();
			for (VariableNameDeclaration var : vars) {
				if (var.getVariable() == variable) {
					return var;
				}
			}
		}
		return null;
	}

	
	/*
	 * 判断domain符合iaoInfo的条件，符合返回true,不符合返回false
	 * 如果domain的域值是unkown，返回false
	 */
	public static boolean isContain(Domain domain, IAOInfo iaoInfo) {
		if(domain == null || domain.getDomaintype()==DomainType.UNKNOWN)
			return false;
		IAOType iaoType = iaoInfo.getIAOType();
		if(domain instanceof IntegerDomain) {
			return intergerIsContain((IntegerDomain)domain, iaoType);
		}
		if(domain instanceof DoubleDomain) {
			return doubleIsContain((DoubleDomain)domain, iaoType);
		}
		return false;
	}
	
	/*
	 * 提供给IAOStateMachine调用的接口
	 * 判断domain符合IAOType的条件，符合返回true,不符合返回false
	 * 如果domain的域值是unkown，返回false
	 */
	public static boolean isContain(Domain domain, IAOType type) {
		if(domain == null || domain.getDomaintype()==DomainType.UNKNOWN)
			return false;
		if(domain instanceof IntegerDomain) {
			return intergerIsContain((IntegerDomain)domain, type);
		}
		if(domain instanceof DoubleDomain) {
			return doubleIsContain((DoubleDomain)domain, type);
		}
		return false;
	}
	
	/*
	 * 给定一个double类型的变量的域值，判断是否只存在iaoTpye
	 */
	public static boolean doubleIsContain(DoubleDomain domain, IAOType iaoType) {
		TreeSet<DoubleInterval> intervalSets = domain.getIntervals();
		Iterator<DoubleInterval> itr = intervalSets.iterator();
		while(itr.hasNext()) {
			DoubleInterval interval = itr.next();
			if(isContain(interval, iaoType)) {
				return true;
			}
		}
		return false;
	}

	/*
	 * 给定一个Double型interval，判定是否存在iaoType
	 */
	private static boolean isContain(DoubleInterval interval, IAOType iaoType) {
		double max = interval.getMax();
		double min = interval.getMin();
		//变量初始化为[-inf, inf]
		if(max == DoubleDomain.DEFAULT_MAX && min == DoubleDomain.DEFAULT_MIN) 
			return true;
		boolean isContainZero = interval.contains(0);	
		switch(iaoType) {
		case NO_ZERO:
			if(isContainZero)
				return true;
			break;
		case NO_BELOW_ZERO:
			if(min < 0)
				return true;
			break;
		case ABOVE_ZERO:
			if(min <= 0)
				return true;
			break;
		case TRI_LIMIT:
			if(min < -1 || max > 1)
				return true;
			break;
		}
		return false;
	}

	/*
	 * 给定一个整型变量的域值，判断是否只存在iaoTpye
	 */
	public static boolean intergerIsContain(IntegerDomain domain, IAOType iaoType) {
		TreeSet<IntegerInterval> intervalSets = domain.getIntervals();
		Iterator<IntegerInterval> itr = intervalSets.iterator();
		while(itr.hasNext()) {
			IntegerInterval interval = itr.next();
			if(isContain(interval, iaoType)) {
				return true;
			}
		}
		return false;
	}
	
	/*
	 * 给定一个整型interval，判定是否存在iaoType
	 */
	private static boolean isContain(IntegerInterval interval, IAOType iaoType) {
		long max = interval.getMax();
		long min = interval.getMin();
		//变量初始化为[-inf, inf]
		if(max == IntegerDomain.DEFAULT_MAX && min == IntegerDomain.DEFAULT_MIN) 
			return true;	// fixed by cmershen,2017.6.1
		boolean isContainZero = interval.contains(0);	
		switch(iaoType) {
		case NO_ZERO:
			if(isContainZero)
				return true;
			break;
		case NO_BELOW_ZERO:
			if(min < 0)
				return true;
			break;
		case ABOVE_ZERO:
			if(min <= 0)
				return true;
			break;
		case TRI_LIMIT:
			if(min < -1 || max > 1)
				return true;
			break;
		}
		return false;
	}

	/*
	 * 状态机实例描述
	 */
	private static void addFSMDescript(FSMMachineInstance fsminstance, SimpleNode snode, FSMMachine fsm, IAOInfo iaoInfo, List<FSMMachineInstance> list) {
		fsminstance.setRelatedASTNode(snode);
		String funcName = iaoInfo.getFuncName();
		fsminstance.setDesp(funcName + "函数调用存在非法计算" );
		fsminstance.setTraceinfo(iaoInfo.getDes());
		list.add(fsminstance);
	}

}
