package softtest.summary.gcc.fault;

import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import softtest.ast.c.ASTCastExpression;
import softtest.ast.c.ASTDeclaration;
import softtest.ast.c.ASTMultiplicativeExpression;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTStatement;
import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.CParserVisitorAdapter;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.VexNode;
import softtest.config.c.Config;
import softtest.domain.c.analysis.ConditionData;
import softtest.domain.c.analysis.ExpressionValueVisitor;
import softtest.domain.c.analysis.ExpressionVistorData;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.DomainType;
import softtest.domain.c.interval.IntegerDomain;
import softtest.domain.c.symbolic.Expression;
import softtest.domain.c.symbolic.SymbolFactor;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.Variable;
import softtest.rules.c.StateMachineUtils;
import softtest.rules.gcc.fault.IAOFunction;
import softtest.rules.gcc.fault.IAO_PREStateMachine;
import softtest.summary.c.MethodFeatureVisitor;
import softtest.summary.c.MethodSummary;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.Search;
import softtest.symboltable.c.VariableNameDeclaration;


public class MethodIAOPreConditionVisitor extends CParserVisitorAdapter implements MethodFeatureVisitor {

	private static MethodIAOPreConditionVisitor instance;
	private MethodNameDeclaration methodDecl = null;
	
	//存在if判断语句中受限的全局/参变量
	private Set<SymbolFactor> ifVarSet = null;
	
	private MethodIAOPreConditionVisitor() {	
	}
	
	public static MethodIAOPreConditionVisitor getInstance() {
		if (instance == null) {
			instance = new MethodIAOPreConditionVisitor(); 
		}
		return instance;
	}
	
	public void visit(VexNode vexNode) {
		if (vexNode.getTreenode() == null) {
			return;
		}
		MethodIAOPreCondition feature = new MethodIAOPreCondition();	
		SimpleNode node = vexNode.getTreenode();
		methodDecl = InterContext.getMethodDecl(vexNode);
		
		ifVarSet = new HashSet<SymbolFactor>();
		//找到存在if判断语句中受限的全局/参变量
		findExistIfStatementVar(node);
		if(node==null || feature==null){
			return;
		}
		if (methodDecl != null) {
			node.jjtAccept(this, feature);
		}
		if (feature.isEmpty()) {
			return;
		}
		// 将计算出的函数特性添加到函数摘要中
		MethodSummary summary = InterContext.getMethodSummary(vexNode);
		if (summary != null) {
			summary.addPreCondition(feature);
			if (Config.INTER_METHOD_TRACE) {
				if (methodDecl != null) {
					System.err.println(methodDecl.getFullName() + " " + feature);
				}
			}
		}
	}
	
	//找到存在if判断语句中受限的全局/参变量
	private void findExistIfStatementVar(SimpleNode treeNode) {
		String if_xpath = ".//SelectionStatement[@Image='if']";
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(treeNode, if_xpath);
		Iterator<SimpleNode> itr = evaluationResults.iterator();
		while(itr.hasNext()) {
			SimpleNode snode = itr.next();
			VexNode vex = snode.getConcreteNode().getCurrentVexNode();
			if(vex == null || vex.getCondata() == null || vex.getCondata().getDomainsTable() == null ) {
				continue;
			}
			ConditionData conData=vex.getCondata();
			Set<SymbolFactor> syms= conData.getDomainsTable().keySet();
			for(SymbolFactor sym: syms) {
				//如果已经存在于ifVarSet中的话，跳过
				//如果不是非局部变量应该跳过，但由于此处通过符号无法获取变量信息 ，有待处理
				if(ifVarSet.contains(sym))
					continue;
				//如果if判断中存在var变量Must受限Domain不是unknown，也不是empty
				if(conData.getMustDomain(sym) != null && !conData.getMustDomain(sym).equals(new IntegerDomain(IntegerDomain.DEFAULT_MIN,IntegerDomain.DEFAULT_MIN)) && !conData.isMustContradict()) {
					ifVarSet.add(sym);	
				}
			}
		}
	}

	/**
	 * 1. 处理对[/]、[/=]、[%]、[%=]的操作
	 * 2. 处理math库下涉及非法计算的函数操作
	 */
	@Override
	public Object visit(ASTStatement node, Object data) {		
		MethodIAOPreCondition feature = (MethodIAOPreCondition)data;
			
		//1： 处理对[/]、[/=]、[%]、[%=]的操作，仅处理分母直接是单个变量，非表达式
		String xpath = ".//MultiplicativeExpression[@Operators='/' or @Operators='%'] |.//AssignmentExpression/AssignmentOperator[@Operators='/=' or @Operators='%=']";
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		for (SimpleNode snode : evaluationResults) {
			//对MultiplicativeExpression和AssignmentExpression区分
			if (snode instanceof ASTMultiplicativeExpression) {
				if(snode.jjtGetNumChildren() != 2)
					continue;
			}else{
				if(snode.jjtGetParent().jjtGetNumChildren() != 3)
					continue;
			}
			ExpressionValueVisitor expvst = new ExpressionValueVisitor();
			ExpressionVistorData visitdata = new ExpressionVistorData();
			visitdata.currentvex = snode.getCurrentVexNode();
			visitdata.currentvex.setfsmCompute(true);
			Domain mydomain=null;
			Object re=null;
			if(snode instanceof ASTMultiplicativeExpression){
				//expvst.visit((SimpleNode)snode.jjtGetChild(1), visitdata);
				//add by zl,20110919
				ASTUnaryExpression aaa;
				if(snode.jjtGetChild(1) instanceof ASTCastExpression)
				{
					aaa=(ASTUnaryExpression)((SimpleNode)snode.jjtGetChild(1)).getFirstDirectChildOfType(ASTUnaryExpression.class);
					if(aaa==null)
					{
						aaa = (ASTUnaryExpression)snode.jjtGetChild(0);
					}
				}else
				{
					aaa = (ASTUnaryExpression)snode.jjtGetChild(1);					
				}
				expvst.visit((SimpleNode)aaa.jjtGetChild(0), visitdata);
				if(aaa.jjtGetChild(0).jjtGetNumChildren()==1)
					re=((SimpleNode)snode.jjtGetChild(1)).getVariableNameDeclaration();
				else if(aaa.jjtGetChild(0).jjtGetNumChildren()==2)
					re=Search.searchInVariableAndMethodUpward(((SimpleNode)aaa.jjtGetChild(0)).getImage(), snode.getScope());
				//re = ((SimpleNode)snode.jjtGetChild(1)).getVariableNameDeclaration();
				//end add 
				visitdata.currentvex.setfsmCompute(false);
				Expression value1 = visitdata.value;
				if(value1!=null)
				mydomain = value1.getDomain(visitdata.currentvex.getSymDomainset());
			}else{
				expvst.visit((SimpleNode)snode.jjtGetParent().jjtGetChild(2), visitdata);
				re = ((SimpleNode)snode.jjtGetParent().jjtGetChild(2)).getVariableNameDeclaration();
				visitdata.currentvex.setfsmCompute(false);
				Expression value1 = visitdata.value;
				if(value1!=null)
				mydomain = value1.getDomain(visitdata.currentvex.getSymDomainset());
			}
			if(!(re instanceof VariableNameDeclaration))
				continue;
			VariableNameDeclaration varDecl = (VariableNameDeclaration)re;
			isIAOVar(node, varDecl, mydomain, IAOType.NO_ZERO, feature, null);
		}
		
		
		//2: 针对库函数,仅处理单个变量作为库函数的参数出现
		//如f(int i){ div(1, i); }可处理; 而f2(int i){ div(1, i+5); }不可处理
		xpath = ".//PrimaryExpression[@Method='true']";
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		//得到math库下可能IAO的函数信息
		List<IAOFunction> iaoFuncList = IAOFunction.getIAOList(); 
		
		for (SimpleNode snode : evaluationResults) {
			MethodNameDeclaration method = StateMachineUtils.getMethodNameDeclaration(snode);
			if(method == null || !method.isLib()) //只处理系统库函数
				continue;
			
			String methodName = method.getImage();
			IAOFunction function = null; //记录当前节点是math库下的哪个函数
			for(IAOFunction iaoFunc : iaoFuncList) {
				if(methodName.equals(iaoFunc.getFuncName())) {
					function = iaoFunc;
					break;
				}
			}
			if(function == null)
				continue;
			
			//得到该库函数可能出现IAO的实参AST节点
			SimpleNode param = null;
			if(snode instanceof ASTPrimaryExpression) {
				param = StateMachineUtils.getArgument(snode, function.getParamIndex());	
			}
			else {
				SimpleNode decl = (SimpleNode) snode.getFirstParentOfType(ASTDeclaration.class);
				param = (SimpleNode) decl.jjtGetChild(1);
			}
			//对实参AST节点进行区间运算
			ExpressionValueVisitor expvst = new ExpressionValueVisitor();
			ExpressionVistorData visitdata = new ExpressionVistorData();
			visitdata.currentvex = param.getCurrentVexNode();
			if(visitdata.currentvex!=null){
				visitdata.currentvex.setfsmCompute(true);
			}
			expvst.visit(param, visitdata);
			visitdata.currentvex.setfsmCompute(false);
			Expression value1 = visitdata.value;
			Domain mydomain=null;
			if(value1!=null)
			mydomain = value1.getDomain(visitdata.currentvex.getSymDomainset());
			Object re = param.getVariableNameDeclaration();
			if(!(re instanceof VariableNameDeclaration))
				continue;
			VariableNameDeclaration varDecl = (VariableNameDeclaration)re;
			isIAOVar(node, varDecl, mydomain, function.getType(), feature, null);
		}
		return super.visit(node, data);
	}
	
	
	private String getType(IAOType type) {
		switch(type) {
			case ABOVE_ZERO:
				return new String("大于0");
			case NO_ZERO:
				return new String("非0");
			case NO_BELOW_ZERO:
				return new String("大于等于0");
			case TRI_LIMIT:
				return new String("变量取值应为[-1,1]");
		}
		return new String("");
	}

	/** 
	 * 处理自定义函数被调用过程所导致的IAO传播
	 */
	@Override
	public Object visit(ASTPrimaryExpression node, Object data) {
		MethodIAOPreCondition feature = (MethodIAOPreCondition)data;
		if (node.isMethod() && node.getMethodDecl()!= null) {
			// 被调用函数可能有IAO的前置约束
			MethodNameDeclaration calledMethod = (MethodNameDeclaration)node.getMethodDecl();
			if(calledMethod.getMethodSummary() == null)
				return null;
			// 检查被调用函数中是否有对形参的IAO前置约束
			MethodIAOPreCondition iaoPreCond = (MethodIAOPreCondition) calledMethod.getMethodSummary().findMethodFeature(MethodIAOPreCondition.class);
			if(iaoPreCond == null || iaoPreCond.isEmpty())
				return null;	
			Set<Variable> vars = iaoPreCond.getIAOVariables();			
			for(Variable var: vars) {
				MethodIAOPreCondition.IAOInfo info = iaoPreCond.getIAOInfo(var);
				IAOType type = info.getIAOType();
				if(var.isParam()) {
					//得到实参
					SimpleNode argNode = StateMachineUtils.getArgument(node, var.getParamIndex());
					ExpressionValueVisitor expvst = new ExpressionValueVisitor();
					ExpressionVistorData visitdata = new ExpressionVistorData();
					visitdata.currentvex = argNode.getCurrentVexNode();
					visitdata.currentvex.setfsmCompute(true);
					expvst.visit(argNode, visitdata);
					visitdata.currentvex.setfsmCompute(false);
					Expression value1 = visitdata.value;
					Domain mydomain=null;
					if(value1!=null)
					mydomain = value1.getDomain(visitdata.currentvex.getSymDomainset());
					Object re = argNode.getVariableNameDeclaration();
					if(!(re instanceof VariableNameDeclaration))
						continue;
					VariableNameDeclaration varDecl = (VariableNameDeclaration)re;
					String traceStr = "。由于该函数调用了" + calledMethod.getImage() + " 函数，" +info.getDes();
					isIAOVar(node, varDecl, mydomain, type, feature, traceStr);
				} else {
					//得到全局变量或类成员变量
					VariableNameDeclaration varDecl = IAO_PREStateMachine.findLocalVariableDecl(var, node);
					if(varDecl != null && node.getCurrentVexNode()!= null) {
						Domain domain = node.getCurrentVexNode().getDomain(varDecl);
						//如果调用该函数前，该变量未出现过，或者该变量出现过但是unknown，变量域相当于unknown, IAO传播
						if(domain == null ||domain.getDomaintype()==DomainType.UNKNOWN) {
							String traceStr = "。由于该函数调用了" + calledMethod.getImage() + " 函数，" +info.getDes();
							isIAOVar(node, varDecl, null, type, feature, traceStr);
						}
					}
				}
			}	
		}
		return null;
	}
	
	public  boolean isIAOVar(SimpleNode node, VariableNameDeclaration varDecl, Domain myDomain, IAOType type, MethodIAOPreCondition feature, String trace) {
		//得到当前varDecl对应的全局变量或者是参变量或者是成员变量
		Variable var = Variable.getVariable(varDecl);
		if(var == null)
			return false;
		String restrict = getType(type);	
		//跟踪信息
		String traceStr = new String("");
		if(trace != null)
			traceStr = trace;
		
		//如果变量是非局部变量，而且domain域是unknown
		if(myDomain == null || myDomain.isUnknown() ||  myDomain.equals(new IntegerDomain(IntegerDomain.DEFAULT_MIN,IntegerDomain.DEFAULT_MAX))) {
			//关于ZX_IAO_PRE_8.cpp这类IAO应该上报,不能作为函数摘要信息存储
			if(ifVarSet.contains(varDecl)) {
				return false;
			}
			String des = null;	
			if(var.isParam()) {	
				des = methodDecl.getImage() + "函数对其第" + (var.getParamIndex()+1) + "参变量的约束类型为" + restrict + traceStr;
			}else {
				des = methodDecl.getImage() + "函数对全局变量" + var.getName() +"约束类型为" + restrict + traceStr;
			}
			feature.addVariable(var, type, methodDecl.getImage(), des);
			return true;
		}
		return false;
	}
	
}
