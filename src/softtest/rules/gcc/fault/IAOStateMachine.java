package softtest.rules.gcc.fault;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.TreeSet;

import softtest.domain.c.analysis.*;
import softtest.ast.c.*;
import softtest.cfg.c.VexNode;
import softtest.domain.c.interval.*;
import softtest.domain.c.symbolic.Expression;
import softtest.domain.c.symbolic.IntegerFactor;
import softtest.domain.c.symbolic.SymbolFactor;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.fsm.c.FSMRelatedCalculation;
import softtest.rules.c.BasicStateMachine;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.NameDeclaration;
import softtest.symboltable.c.NameOccurrence;
import softtest.symboltable.c.Scope;
import softtest.symboltable.c.Search;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.summary.gcc.fault.IAOType;


public class IAOStateMachine extends BasicStateMachine {

	@Override
	public void registFetureVisitors() {
		super.registFetureVisitors();
	}
	static int i=1;
	public static List<FSMMachineInstance> createIAOStateMachines(
			SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		String xPath = ".//PostfixExpression/PrimaryExpression[(";
		for (int i = 0; i < mathFunction.length; i++) {
			xPath += "@Image='" + mathFunction[i] + "' or "; 
		}
		if (mathFunction.length > 0) {
			xPath = xPath.substring(0, xPath.length() - 3);
		}
		xPath += ")]" 
			    + "|.//MultiplicativeExpression[@Operators='/' or @Operators='%']"
				+ "|.//AssignmentExpression/AssignmentOperator[@Operators='/=' or @Operators='%=']";
		
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);
		if(evaluationResults!=null){
			for (SimpleNode snode : evaluationResults) {
				if (snode instanceof ASTPrimaryExpression || snode instanceof ASTDirectDeclarator) {
					AbstractExpression abstNode = (AbstractExpression)snode;
					if (!abstNode.isMethod()) {
						continue;
					}
				}
				FSMMachineInstance fsminstance = fsm.creatInstance();
				fsminstance.setRelatedASTNode(snode);
				fsminstance.setRelatedObject(new FSMRelatedCalculation(snode));
				list.add(fsminstance);
//				System.out.println("《测试IAO》这是产生的第"+i+"个IAO状态机实例，在第 "+ snode.getBeginLine() + "行，第"+snode.getBeginColumn()+"列满足状态机产生条件 ");
//				i++;
			}
		}
		return list;
	}

	// function type mean:
	// 1000. 参数为1个，取值范围为[-1,1]
	// 1100. 参数为1个，取值范围为>0
	// 1200. 参数为1个，取值范围为>=0
	// 2000. 参数为2个，第2个参数的取值范围为!=0
	private static String[] mathFunction = { "acos", "asin", "log", "log10",
			"sqrt", "ldiv", "div", "fmod", "atan2" };

	private static int[] mathFunctionType = { 1000, 1000, 1100, 1100, 1200,
			2000, 2000, 2000, 2000 };

	/**
	 *  根据不同的函数计算相应的区间运算结果 
	 */
	private static boolean CheckFunctionType(int functionTypeID, Domain myDomain) {
		double maxValue = 0, minValue = 0;
		boolean isContainZero = false;
		if (myDomain.domaintype == DomainType.DOUBLE) {
			DoubleDomain myDoubleDomain = (DoubleDomain) myDomain;
			maxValue = myDoubleDomain.jointoOneInterval().getMax();
			minValue = myDoubleDomain.jointoOneInterval().getMin();
			isContainZero = myDoubleDomain.contains(0);
		} else if (myDomain.domaintype == DomainType.INTEGER) {
			IntegerDomain myIntDomain = (IntegerDomain) myDomain;
			maxValue = myIntDomain.jointoOneInterval().getMax();
			minValue = myIntDomain.jointoOneInterval().getMin();
			isContainZero = myIntDomain.contains(0);
		} else {
			return false;
		}

		switch (functionTypeID) {
		case 1000:
			if (minValue < -1 || maxValue > 1) {
				return true;
			}
			break;
		case 1100:
			if (minValue <= 0) {
				return true;
			}
			break;
		case 1200:
			if (minValue < 0) {
				return true;
			}
			break;
		case 2000:
			if (isContainZero) {
				return true;
			}
			break;
		default:
			break;
		}
		return false;
	}
	
	/** 
	 * 检查各个函数的取值是否包括非法数值 PrimaryExpression 
	 */
	public static boolean checkPrimaryExpression(List nodes, FSMMachineInstance fsmin) {
		Iterator nodeIterator = nodes.iterator();
		while (nodeIterator.hasNext()) {
			ASTPrimaryExpression snode = (ASTPrimaryExpression) nodeIterator.next();
			
			if (snode != fsmin.getRelatedASTNode()) {
				continue;
			}
			if(snode.getCurrentVexNode().getContradict()){
				return false;
			}
			String funName = snode.getImage();
			int functionTypeID = -1;
			for (int i = 0; i < mathFunction.length; i++) {
				if (mathFunction[i].equals(funName)) {
					functionTypeID = mathFunctionType[i];
					break;
				}
			}
			if (functionTypeID == -1) // type not find
			{
				return false;
			}

			ExpressionValueVisitor expvst = new ExpressionValueVisitor();
			ExpressionVistorData visitdata = new ExpressionVistorData();
			visitdata.currentvex = snode.getCurrentVexNode();
			visitdata.currentvex.setfsmCompute(true);
			Domain mydomain=null;
			
			// get argue list //参数列表
			SimpleNode parent = (SimpleNode)snode.jjtGetParent();
			if (parent.jjtGetNumChildren() != 2 || !(parent.jjtGetChild(1) instanceof ASTArgumentExpressionList)) {
				return false;
			}
			ASTArgumentExpressionList argue = (ASTArgumentExpressionList) parent.jjtGetChild(1);
			ASTAssignmentExpression arguexx = null;
			if (functionTypeID == 2000) {
				expvst.visit((SimpleNode)argue.jjtGetChild(1), visitdata);
				visitdata.currentvex.setfsmCompute(false);
				Expression value1 = visitdata.value;
				if(value1!=null)
				mydomain = value1.getDomain(visitdata.currentvex.getSymDomainset());
				arguexx=(ASTAssignmentExpression)argue.jjtGetChild(1);
			} else {
				expvst.visit((SimpleNode)argue.jjtGetChild(0), visitdata);
				visitdata.currentvex.setfsmCompute(false);
				Expression value1 = visitdata.value;
				if(value1!=null)
				mydomain = value1.getDomain(visitdata.currentvex.getSymDomainset());
				arguexx=(ASTAssignmentExpression)argue.jjtGetChild(0);
			}
			if (mydomain == null || mydomain.equals(new IntegerDomain(IntegerDomain.DEFAULT_MIN,IntegerDomain.DEFAULT_MAX))){
				return false;
			}
			boolean isError = CheckFunctionType(functionTypeID, mydomain);
			
			if (isError) {		
				fsmin.setDesp("在第 "+ snode.getBeginLine() + "行函数"+snode.getImage()+"的参数"+arguexx.getImage()+"取值范围超过条件，存在关于函数 " + snode.getImage() + " 的非法计算。");
				fsmin.setNodeUseToFindPosition(snode);
			}
			return isError;
		}
		return false;
	}
	
	/** 
	 * 检查运算符 / 和 %的除数的取值是否包括非法取值,
	 * 以及类似 检查运算符 /= 和 %=的表达式
	 */
	public static boolean checkIaoExpression(List<SimpleNode> nodes, FSMMachineInstance fsmin) {
		Iterator<SimpleNode> nodeIterator = nodes.iterator();
		String varImage=null;
		while (nodeIterator.hasNext()) {
            SimpleNode snode = (SimpleNode) nodeIterator.next();
			if (snode==null || snode != fsmin.getRelatedASTNode()) {
				continue;
			}
			
			ExpressionValueVisitor expvst = new ExpressionValueVisitor();
			ExpressionVistorData visitdata = new ExpressionVistorData();
			visitdata.currentvex = snode.getCurrentVexNode();
			visitdata.currentvex.setfsmCompute(true);
			Domain mydomain=null;
			
			ArrayList<String> opts = snode.getOperatorType();
			if (opts == null || opts.size() == 0) {
				return false;
			}
			String opt = opts.get(0);
			if (!opt.equals("/") && !opt.equals("%") && !opt.equals("/=") && !opt.equals("%=")) {
				return false;
			}
			//对MultiplicativeExpression和AssignmentExpression区分
			if (snode instanceof ASTMultiplicativeExpression) {
				if(snode.jjtGetNumChildren() != 2)
					return false;
			}else{
				if(snode.jjtGetParent()!=null && snode.jjtGetParent().jjtGetNumChildren() != 3)
					return false;
			}
			Object re=null;
			if(snode instanceof ASTMultiplicativeExpression){
				if((SimpleNode)snode.jjtGetChild(1) instanceof ASTUnaryExpression){
					ASTUnaryExpression aaa=(ASTUnaryExpression)((SimpleNode)snode.jjtGetChild(1));
					
					expvst.visit((SimpleNode)aaa.jjtGetChild(0), visitdata);
					if(aaa.jjtGetChild(0).jjtGetNumChildren()==1)
						re=((SimpleNode)snode.jjtGetChild(1)).getVariableNameDeclaration();
					else if(aaa.jjtGetChild(0).jjtGetNumChildren()==2)
						re=Search.searchInVariableAndMethodUpward(((SimpleNode)aaa.jjtGetChild(0)).getImage(), snode.getScope());
					
					visitdata.currentvex.setfsmCompute(false);
					Expression value1 = visitdata.value;
					if(value1!=null){
						mydomain = value1.getDomain(visitdata.currentvex.getSymDomainset());
					}
				}else if((SimpleNode)snode.jjtGetChild(1) instanceof ASTCastExpression){
					
				}
			}else{
				expvst.visit((SimpleNode)snode.jjtGetParent().jjtGetChild(2), visitdata);
				re = ((SimpleNode)snode.jjtGetParent().jjtGetChild(2)).getVariableNameDeclaration();
				visitdata.currentvex.setfsmCompute(false);
				Expression value1 = visitdata.value;
				if(value1!=null)
				mydomain = value1.getDomain(visitdata.currentvex.getSymDomainset());
				
			}
			
			//避免a = 1/a;情况,赋值表达式右边a为0，而赋值表达式左边的a为[-inf, inf]
			if(re instanceof VariableNameDeclaration) {
				
				VariableNameDeclaration var = (VariableNameDeclaration) re;
				VexNode curNode = snode.getConcreteNode().getCurrentVexNode();
				//zl,针对测试用例35
				
				if(curNode == null || mydomain==null ||var==null)
					return false;
				Domain domain =  curNode.getDomain(var);
				if(var.getDomain()==null && var.isParam() &&!(mydomain.isUnknown())){
					if(domain instanceof IntegerDomain){
						IntegerDomain intDomain=(IntegerDomain)domain;
						TreeSet<IntegerInterval> intervalSets=((IntegerDomain) domain).getIntervals();
						Iterator<IntegerInterval> itr = intervalSets.iterator();
						IntegerInterval interval = itr.next();
						if(isContainParam( interval, IAOType.NO_ZERO)){
							fsmin.setDesp("在第 "+ snode.getBeginLine() + "行，变量"+var.getImage()+"的取值可能为0，存在关于操作符'" + opt + "'的非法计算。");
							//added by cmershen,2016.3.21
							fsmin.setVarImage(var.getImage());
							return true;
						}
					}
				}
				if(IAO_PREStateMachine.isContain(domain, IAOType.NO_ZERO)) {
					if (!confirmIAO(snode, var)) {
						return false;
					}
					fsmin.setDesp("在第 "+ snode.getBeginLine() + "行，变量"+var.getImage()+"的取值可能为0，存在关于操作符'" + opt + "'的非法计算。");
					//added by cmershen,2016.3.21
					fsmin.setVarImage(var.getImage());
					return true;
				}
				if(domain != null) { 
					return false;
				}
			}
			if (mydomain==null|| mydomain.equals(new IntegerDomain(IntegerDomain.DEFAULT_MIN,IntegerDomain.DEFAULT_MAX))){
				return false;
			}
			boolean iscontainZero = false;
			if (mydomain.domaintype == DomainType.INTEGER) {
				if (((IntegerDomain) mydomain).contains(0)) {
					iscontainZero = true;
				}
			}
			if (iscontainZero) {
				// 检查是否有短路
				varImage=null;
				if (re instanceof VariableNameDeclaration) {
					if (!confirmIAO(snode, (VariableNameDeclaration)re)) {
						return false;
					}
					varImage=((VariableNameDeclaration)re).getImage();
				}else if(re instanceof NameDeclaration){
					varImage=((NameDeclaration)re).getImage();
				}
				fsmin.setDesp("在第 "+ snode.getBeginLine() + "行，变量"+varImage+"的取值可能为0，存在关于操作符'" + opt + "'的非法计算。");
				//added by cmershen,2016.3.21
				fsmin.setVarImage(varImage);
				if(snode instanceof ASTMultiplicativeExpression){
					fsmin.setNodeUseToFindPosition((SimpleNode)snode.jjtGetChild(1));
				}else{
					fsmin.setNodeUseToFindPosition((SimpleNode)snode.jjtGetParent().jjtGetChild(2));
				}
				return true;
			}
			return false;
		}
		return false;
	}
	
	public static boolean confirmIAO(SimpleNode idExp, VariableNameDeclaration vDecl) {
		//check the condition expression eg: int j = (p == 0)? i: p/a;
		ASTConditionalExpression con = (ASTConditionalExpression) idExp.getFirstParentOfType(ASTConditionalExpression.class);
		if (con != null) {
			String str = ".//PostfixExpression/PrimaryExpression";
			if((SimpleNode)con.jjtGetChild(0)!=null){
				List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults((SimpleNode)con.jjtGetChild(0), str);
				Iterator<SimpleNode> iterList = evaluationResults.iterator();
				while(iterList.hasNext()){
					ASTPrimaryExpression temp = (ASTPrimaryExpression) iterList.next();
					if(temp.getVariableNameDeclaration()!= vDecl){
						continue;
					}
					ASTEqualityExpression equal = (ASTEqualityExpression)temp.getFirstParentOfType(ASTEqualityExpression.class);
					if(equal == null || equal.jjtGetNumChildren()>1){
						return false;
					}					
				}
			}
		}
		// 检查表达式短路: if (p!=0 && a/p) 或者 if (p && a/p)
		ASTLogicalANDExpression expressionAnd = (ASTLogicalANDExpression)idExp.getFirstParentOfType(ASTLogicalANDExpression.class);
		if (expressionAnd != null && expressionAnd.jjtGetNumChildren() >= 2) {
			for (int i = 0; i < expressionAnd.jjtGetNumChildren(); i++) {
				SimpleNode expNode = (SimpleNode)expressionAnd.jjtGetChild(i);
				if (idExp.isSelOrAncestor(expNode)) {
					break;
				}
				// p 的may集合是不是为非空
				ConditionDomainVisitor condVisitor = new ConditionDomainVisitor();
				ConditionData condData=new ConditionData(idExp.getCurrentVexNode());
				expNode.jjtAccept(condVisitor, condData);
				Domain pDomain=null;
				if(vDecl==null || idExp==null || idExp.getCurrentVexNode()==null || idExp.getCurrentVexNode().getValue(vDecl)==null || idExp.getCurrentVexNode().getValue(vDecl).getSingleFactor()==null){
					continue;
				}
				if(idExp.getCurrentVexNode().getValue(vDecl).getSingleFactor() instanceof SymbolFactor)
				{
					pDomain = condData.getMayDomain((SymbolFactor) idExp.getCurrentVexNode().getValue(vDecl).getSingleFactor());
				}else if(idExp.getCurrentVexNode().getValue(vDecl).getSingleFactor() instanceof IntegerFactor)
				{
					//pDomain=idExp.getCurrentVexNode().getDomain(vDecl);
				}
				if (pDomain != null && pDomain instanceof IntegerDomain &&  !(pDomain.equals(new IntegerDomain(IntegerDomain.DEFAULT_MIN,IntegerDomain.DEFAULT_MAX)))) {
					IntegerDomain integer = (IntegerDomain)pDomain;
					if (integer.isEmpty() || !integer.contains(0)) {
						return false;
					}
				}
				// 判断是否有恒假分支
				ExpressionValueVisitor expvst = new ExpressionValueVisitor();
				ExpressionVistorData visitdata = new ExpressionVistorData();
				visitdata.currentvex = expNode.getCurrentVexNode();
				visitdata.currentvex.setfsmCompute(true);
				expvst.visit(expNode, visitdata);
				visitdata.currentvex.setfsmCompute(false);
				Expression value1 = visitdata.value;
				Domain mydomain=null;
				if(value1!=null)
				mydomain = value1.getDomain(visitdata.currentvex.getSymDomainset());
//				if (mydomain instanceof BooleanDomain) {
//					BooleanDomain bDomain = (BooleanDomain)domaindata.domain;
//					if (bDomain.getValue() == BooleanValue.FALSE) {
//						return false;
//					}
//				} else 
					if (mydomain instanceof IntegerDomain &&  !(mydomain.equals(new IntegerDomain(IntegerDomain.DEFAULT_MIN,IntegerDomain.DEFAULT_MAX)))) {
					IntegerDomain iDomain = (IntegerDomain)mydomain;
					if (iDomain.isCanonical() && iDomain.contains(0)) {
						return false;
					}
				}
			}
		}
		// 检查表达式短路: if(!p || a/p) 或者 if (p == 0 ||  a/p)  
		ASTLogicalORExpression expressionOr = (ASTLogicalORExpression)idExp.getFirstParentOfType(ASTLogicalORExpression.class);
		if (expressionOr != null && expressionOr.jjtGetNumChildren() >= 2) {
			for (int i = 0; i < expressionOr.jjtGetNumChildren(); i++) {
				SimpleNode expNode = (SimpleNode)expressionOr.jjtGetChild(i);
				if (idExp.isSelOrAncestor(expNode)) {
					break;
				}
				
				// p 的must集合是是空
				ConditionDomainVisitor condVisitor = new ConditionDomainVisitor();
				ConditionData condData = new ConditionData(idExp.getCurrentVexNode());
				expNode.jjtAccept(condVisitor, condData);
				Domain pDomain = condData.getMustDomain((SymbolFactor) idExp.getCurrentVexNode().getValue(vDecl).getSingleFactor());
				if (pDomain != null && pDomain instanceof IntegerDomain &&  !(pDomain.equals(new IntegerDomain(IntegerDomain.DEFAULT_MIN,IntegerDomain.DEFAULT_MAX)))) {
					IntegerDomain integer = (IntegerDomain)pDomain;
					if (integer.isCanonical() && integer.contains(0) ) {
						return false;
					}
				}
				// 判断是否有恒真分支
				ExpressionValueVisitor expvst = new ExpressionValueVisitor();
				ExpressionVistorData visitdata = new ExpressionVistorData();
				visitdata.currentvex = expNode.getCurrentVexNode();
				visitdata.currentvex.setfsmCompute(true);
				expvst.visit(expNode, visitdata);
				visitdata.currentvex.setfsmCompute(false);
				Expression value1 = visitdata.value;
				Domain mydomain=null;
				if(value1!=null)
				mydomain = value1.getDomain(visitdata.currentvex.getSymDomainset());
//				if (mydomain instanceof BooleanDomain) {
//					BooleanDomain bDomain = (BooleanDomain)domaindata.domain;
//					if (bDomain.getValue() == BooleanValue.TRUE) {
//						return false;
//					}
//				} else 
					if (mydomain instanceof IntegerDomain &&  !(mydomain.equals(new IntegerDomain(IntegerDomain.DEFAULT_MIN,IntegerDomain.DEFAULT_MAX)))) {
					IntegerDomain iDomain = (IntegerDomain)mydomain;
					if (iDomain.isCanonical() && !iDomain.contains(0)) {
						return false;
					}
				}
			}
		}
		
		//检查变量前一次区间的改变是否发生在循环中
		NameOccurrence occ = idExp.getCurrentVexNode().getVariableNameOccurrence(vDecl);
		if(occ != null) {
			Scope scope = vDecl.getScope();
			if(scope != null) {
				List<NameOccurrence> occs = scope.getVariableDeclarations().get(vDecl);
				if(occs != null) {
					int index = -1;
					for(int i = 0; i < occs.size(); i++) {
						if(occs.get(i).getLocation() == occ.getLocation()) {
							index = i;
							break;
						}
					}
					if(index >= 2) {
						NameOccurrence lastOcc = occs.get(index - 1);
						if(lastOcc.getLocation().getParentsOfType(ASTIterationStatement.class).size() != 0)
							return false;
					}
				}
			}
		}
		return true;
	}
	
	/*
	 * 给定一个整型interval，判定是否存在iaoType,针对变量是参数的情况
	 */
	private static boolean isContainParam(IntegerInterval interval, IAOType iaoType) {
		long max = interval.getMax();
		long min = interval.getMin();
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
}
