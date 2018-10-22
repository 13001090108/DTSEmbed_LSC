package softtest.domain.c.analysis;

import java.util.List;

import org.apache.log4j.Logger;

import softtest.ast.c.*;
import softtest.cfg.c.VexNode;
import softtest.config.c.Config;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.DoubleDomain;
import softtest.domain.c.interval.DoubleMath;
import softtest.domain.c.interval.IntegerDomain;
import softtest.domain.c.interval.PointerDomain;
import softtest.domain.c.interval.PointerValue;
import softtest.domain.c.symbolic.Expression;
import softtest.domain.c.symbolic.Factor;
import softtest.domain.c.symbolic.NumberFactor;
import softtest.domain.c.symbolic.SymbolFactor;
import softtest.domain.c.symbolic.Term;
import softtest.symboltable.c.*;
import softtest.symboltable.c.Type.*;

public class ConditionDomainVisitor extends CParserVisitorAdapter {
	public Object visit(SimpleNode node, Object data) {
		// 阻止访问向孩子传递
		// node.childrenAccept(this, data);
		return null;
	}
	
	public Object visit(ASTExpression node, Object data) {
		//zys:2010.8.11	在条件判断节点，如果超过了语法树深度上限，则不再递归访问其子结点
		int depth=node.getDescendantDepth();
		if(depth<=Config.MAXASTTREEDEPTH){
			node.childrenAccept(this, data);
		}else{
			//Logger.getRootLogger().info("ConditionDomainVisitor: ASTExpression in .i "+node.getBeginFileLine()+" depth="+depth+" overflow");
		}
//		node.childrenAccept(this, data);
		return data;
	}
	
	/**暂时只处理最简单的a+b类型：added by zys 2011.6.20	if(a+b) */
	public Object visit(ASTAdditiveExpression node, Object data){
		if(node.jjtGetNumChildren()==2){
			SimpleNode leftNode=(SimpleNode) node.jjtGetChild(0);
			SimpleNode rightNode=(SimpleNode) node.jjtGetChild(1);
			resetSymbolExpressionForConditionVariable(leftNode);
			resetSymbolExpressionForConditionVariable(rightNode);
		}
		return data;
	}
	
	/**暂时不作任何处理：added by zys 2011.6.20	if(a*b) */
	public Object visit(ASTMultiplicativeExpression node, Object data){
		
		return data;
	}
	
	public Object visit(ASTAssignmentExpression node, Object data) {
		//chh   类似if（a+b）中的a+b这种类型的表达式要在这里进行分析
		SimpleNode child = (SimpleNode) node.jjtGetChild(0);
		if(child!=null&&!(child instanceof ASTCastExpression)
				&&!(child instanceof ASTLogicalORExpression)
				&&!(child instanceof ASTLogicalANDExpression)
				&&!(child instanceof ASTEqualityExpression)
				&&!(child instanceof ASTRelationalExpression)
				&&!(child instanceof ASTUnaryExpression))
		{
			/**Begin: added by zys 2011.6.20 if(a+b)或if(a*b) */
			child.jjtAccept(this, data);
			/**End: added by zys 2011.6.20	if(a+b)或if(a*b) */
			
			ConditionData condata = (ConditionData) data;
			Expression  exp=null;
			ExpressionVistorData expdata = new ExpressionVistorData();
			expdata.currentvex = condata.currentvex;
			expdata.sideeffect = false;
			child.jjtAccept(new ExpressionValueVisitor(), expdata);
			exp=expdata.value;
			
			if(exp!=null && exp.getSingleFactor() instanceof NumberFactor){
				NumberFactor f=(NumberFactor)exp.getSingleFactor();
				Domain may=null,must=null;
				SymbolFactor s=SymbolFactor.genSymbol(CType_BaseType.getBaseType("int"));
				if((f.getDoubleValue()==0)){	
					may=IntegerDomain.getEmptyDomain();
					must=IntegerDomain.getEmptyDomain();
					condata.addMayDomain(s, may);
					condata.addMustDomain(s, must);
				}else{
					may=IntegerDomain.getFullDomain();
					must=IntegerDomain.getFullDomain();
					condata.addMayDomain(s, may);
					condata.addMustDomain(s, must);
				}
				
				return data;
			}
			if(exp==null)
			{
				return data;
			}
			for(Term t:exp.getTerms()){
				Factor f=t.getSingleFactor();
				if(f instanceof SymbolFactor){
					SymbolFactor s=(SymbolFactor)f;
					Expression temp=new Expression(s).sub(exp);
					Domain rightdomain = temp.getDomain(condata.currentvex.getSymDomainset());
					Domain leftdomain=s.getDomainWithoutNull(condata.currentvex.getSymDomainset());
					CType type=s.getType();
					
					if(rightdomain!=null){
						Domain may=null,must=null;
						may = Domain.intersect(leftdomain, rightdomain, type);
						if (rightdomain.isCanonical()) {
							must = Domain.intersect(leftdomain, rightdomain, type);
						} else {
							must = Domain.getEmptyDomainFromType(s.getType());
						}
						
							condata.addMayDomain(s, may);
							condata.addMustDomain(s, must);
						
					}
				}
				//处理系数为-1情况
				f=t.getMinusSingleFactor();
				if(f instanceof SymbolFactor){
					SymbolFactor s=(SymbolFactor)f;
					Expression temp=new Expression(s).add(exp);
					Domain rightdomain = temp.getDomain(condata.currentvex.getSymDomainset());
					Domain leftdomain=s.getDomainWithoutNull(condata.currentvex.getSymDomainset());
					CType type=s.getType();
					
					if(rightdomain!=null){
						Domain may=null,must=null;
						may = Domain.intersect(leftdomain, rightdomain, type);
						if (rightdomain.isCanonical()) {
							must = Domain.intersect(leftdomain, rightdomain, type);
						} else {
							must = Domain.getEmptyDomainFromType(s.getType());
						}
					
							condata.addMayDomain(s, may);
							condata.addMustDomain(s, must);
						
					}
				}
			}
			return data;
		}
		else
		{
			node.childrenAccept(this, data);
			return data;
		}
		//end
	}
	public Object visit(ASTCastExpression node, Object data) {
		node.childrenAccept(this, data);
		return data;
	} 
	
	public Object visit(ASTLogicalORExpression node, Object data) {
		// ||
		if(node.containsChildOfType(ASTPrimaryExpression.class)){
			List<Node> primarys =node.findChildrenOfType(ASTPrimaryExpression.class);
			for(Node pri:primarys){
				if(pri.jjtGetNumChildren()==0){
					VariableNameDeclaration v =((SimpleNode)pri).getVariableNameDeclaration();
					if(v!=null){
						if(v.getType()instanceof CType_Array&&!(((CType_Array)v.getType()).getOriginaltype() instanceof CType_BaseType||((CType_Array)v.getType()).getOriginaltype() instanceof CType_Qualified)||
								(v.getType()instanceof CType_Struct&&pri.jjtGetParent().jjtGetNumChildren()==1)){
							return data;
						}
					}
				}
			}
		}
		ConditionData condata = (ConditionData) data;
		ConditionData leftdata = new ConditionData(condata.currentvex);
		Node currentnode = node.jjtGetChild(0);
		currentnode.jjtAccept(this, leftdata);

		for (int i = 1; i < node.jjtGetNumChildren(); i++) {
			ConditionData rightdata = new ConditionData(condata.currentvex);
			currentnode =  node.jjtGetChild(i);
			currentnode.jjtAccept(this, rightdata);
			leftdata=condata.calLogicalOrExpression(leftdata, rightdata);
		}
		condata.setDomainsTable(leftdata.getDomainsTable());
		return data;
	}
	
	public Object visit(ASTLogicalANDExpression node, Object data) {
		//&&
		ConditionData condata = (ConditionData) data;
		ConditionData leftdata = new ConditionData(condata.currentvex);
		Node currentnode = node.jjtGetChild(0);
		currentnode.jjtAccept(this, leftdata);

		for (int i = 1; i < node.jjtGetNumChildren(); i++) {
			ConditionData rightdata = new ConditionData(condata.currentvex);
			currentnode =  node.jjtGetChild(i);
			currentnode.jjtAccept(this, rightdata);
			leftdata=condata.calLogicalAndExpression(leftdata, rightdata);
		}
		condata.setDomainsTable(leftdata.getDomainsTable());
		return data;
	}
	
	public Object visit(ASTEqualityExpression node, Object data) {
		//== !=
		ConditionData condata = (ConditionData) data;
		if(node.getOperatorType().size()>1){
			return data;
		}
		String operator=node.getOperatorType().get(0);
		SimpleNode left = (SimpleNode) node.jjtGetChild(0);
		SimpleNode right = (SimpleNode) node.jjtGetChild(1);
		
		//begin: modified by zys 2011.6.20
		VariableNameDeclaration leftVar=resetSymbolExpressionForConditionVariable(left);
		VariableNameDeclaration rightVar=resetSymbolExpressionForConditionVariable(right);
		//end: modified by zys 2011.6.20
		
		Expression rightvalue=null,leftvalue=null;
		ExpressionVistorData expdata = new ExpressionVistorData();
		expdata.currentvex = condata.currentvex;
		expdata.sideeffect = false;
		left.jjtAccept(new ExpressionValueVisitor(), expdata);
		leftvalue=expdata.value;
		expdata.value = null;
		right.jjtAccept(new ExpressionValueVisitor(), expdata);
		rightvalue=expdata.value;
		//由于一些数据类型无法处理，故不做区间分析及条件判断
		//add by zhouhb 2010/8/23
//		if(node.containsChildOfType(ASTPrimaryExpression.class)){
//			List<Node> primarys =node.findChildrenOfType(ASTPrimaryExpression.class);
//			for(Node pri:primarys){
//				if(pri.jjtGetNumChildren()==0){
//					VariableNameDeclaration v =((SimpleNode)pri).getVariableNameDeclaration();
//					if(v!=null){
//						if(v.getType()instanceof CType_Pointer&&!(((CType_Pointer)v.getType()).getOriginaltype() instanceof CType_BaseType||((CType_Pointer)v.getType()).getOriginaltype() instanceof CType_Qualified)||
//								v.getType()instanceof CType_Array&&!(((CType_Array)v.getType()).getOriginaltype() instanceof CType_BaseType||((CType_Pointer)v.getType()).getOriginaltype() instanceof CType_Qualified)||
//								v.getType()instanceof CType_Struct){
//							return data;
//						}
//					}
//				}
//			}
//		}
		if(leftvalue==null || rightvalue==null)
		{
			return data;
		}
		
		//add by zhouhb
		//如果操作符两端有一端未知，则不予处理
//		Domain LDomain=leftvalue.getDomain(expdata.currentvex.getSymDomainset());
//		Domain RDomain=rightvalue.getDomain(expdata.currentvex.getSymDomainset());
//		if(LDomain==null||RDomain==null){
//			return data;
//		}

		Expression exp=leftvalue.sub(rightvalue);
		if(exp.getSingleFactor() instanceof NumberFactor){
			NumberFactor f=(NumberFactor)exp.getSingleFactor();
			Domain may=null,must=null;
			SymbolFactor s=SymbolFactor.genSymbol(CType_BaseType.getBaseType("int"));
			if((f.getDoubleValue()==0&&operator.equals("=="))||
					(f.getDoubleValue()!=0&&operator.equals("!="))){
				may=IntegerDomain.getFullDomain();
				must=IntegerDomain.getFullDomain();
				condata.addMayDomain(s, may);
				condata.addMustDomain(s, must);	
			}else{
				may=IntegerDomain.getEmptyDomain();
				must=IntegerDomain.getEmptyDomain();
				condata.addMayDomain(s, may);
				condata.addMustDomain(s, must);	
			}
			return data;
		}
//		if(Config.USEUNKNOWN && (LDomain.isUnknown() && RDomain.isUnknown()) ){
//			return data;
//		}
		for(Term t:exp.getTerms()){
			Factor f=t.getSingleFactor();
			if(f instanceof SymbolFactor){
				SymbolFactor s=(SymbolFactor)f;
				Expression temp=new Expression(s).sub(exp);
				Domain rightdomain = temp.getDomain(condata.currentvex.getSymDomainset());
				//对于空指针，此处取值为0，需做相应类型转换
			    //add by zhouhb 2010/7/19
				if(rightdomain!=null && rightdomain.toString().equals("[0,0]")||expdata.value.toString().equals("0")){
					//由于'\0'通过处理后仍然对应区间为[0,0]，此处不考虑此情况
					//modified by zhouhb 2010/8/23
					ASTConstant con=(ASTConstant)right.getFirstChildOfType(ASTConstant.class);
					if(con!=null && con.getImage().startsWith("\'"))
						return data;
					PointerDomain pDomain=new PointerDomain();
					pDomain.offsetRange.intervals.clear();
					//pDomain.AllocType=CType_AllocType.Null;
					pDomain.Type.add(CType_AllocType.Null);
					pDomain.setValue(PointerValue.NULL);
					rightdomain=pDomain;
				}
				Domain leftdomain=s.getDomainWithoutNull(condata.currentvex.getSymDomainset());
				CType type=s.getType();
				
				if(rightdomain!=null){
					Domain may=null,must=null;
					may = Domain.intersect(leftdomain, rightdomain, type);
					if (rightdomain.isCanonical()) {
						must = Domain.intersect(leftdomain, rightdomain, type);
					} else {
						must = Domain.getEmptyDomainFromType(s.getType());
					}
					if (operator.equals("==")) {
						condata.addMayDomain(s, may);
						condata.addMustDomain(s, must);
					}else{
						Domain temp1=Domain.inverse(must);
						Domain temp2=Domain.inverse(may);
						//对于指针分配空间来说，非空即分配成功，直接继承"!="左边的分配属性即可
						//add by zhouhb 2010/7/19
						if(leftdomain instanceof PointerDomain && rightdomain instanceof PointerDomain && ((PointerDomain)rightdomain).getValue().toString().equals("NULL")){
							if(temp1 instanceof IntegerDomain)
							{
								temp1=Domain.castToType(temp1, new CType_Pointer());
								temp2=Domain.castToType(temp2, new CType_Pointer());
							}							
							((PointerDomain)temp1).offsetRange=((PointerDomain)leftdomain).offsetRange;
							((PointerDomain)temp1).allocRange=((PointerDomain)leftdomain).allocRange;
							((PointerDomain)temp1).Type=((PointerDomain)leftdomain).Type;
							((PointerDomain)temp2).offsetRange=((PointerDomain)leftdomain).offsetRange;
							((PointerDomain)temp2).allocRange=((PointerDomain)leftdomain).allocRange;
							((PointerDomain)temp2).Type=((PointerDomain)leftdomain).Type;
						}
						condata.addMayDomain(s,temp1);
						condata.addMustDomain(s,temp2);
					}
				}
			}
			//处理系数为-1情况
			f=t.getMinusSingleFactor();
			if(f instanceof SymbolFactor){
				SymbolFactor s=(SymbolFactor)f;
				Expression temp=new Expression(s).add(exp);
				Domain rightdomain = temp.getDomain(condata.currentvex.getSymDomainset());
				Domain leftdomain=s.getDomainWithoutNull(condata.currentvex.getSymDomainset());
				CType type=s.getType();
				
				if(rightdomain!=null){
					Domain may=null,must=null;
					may = Domain.intersect(leftdomain, rightdomain, type);
					if (rightdomain.isCanonical()) {
						must = Domain.intersect(leftdomain, rightdomain, type);
					} else {
						must = Domain.getEmptyDomainFromType(s.getType());
					}
					if (operator.equals("==")) {
						condata.addMayDomain(s, may);
						condata.addMustDomain(s, must);
					}else{
						condata.addMayDomain(s, Domain.inverse(must));
						condata.addMustDomain(s, Domain.inverse(may));
					}
				}
			}
		}
		return data;
	}
	
	/**modified by zys 2011.6.20
	 * 修改原因：对于if(x>y)或if(x>0)类似的表达式，如果x或y此处的符号表达式为复杂类型（包括两个或更多的符号s1+s2，或单个符号的非线性表示s1^2 s1*s2,
	 * 此时需要为该条件变量生成新的符号，生成相应的condata*/
	private VariableNameDeclaration resetSymbolExpressionForConditionVariable(SimpleNode n){
		VariableNameDeclaration leftVar=n.getVariableNameDeclaration();
		if(leftVar!=null){
			VexNode vex=n.getCurrentVexNode();
			Expression leftExpr=vex.getValue(leftVar);
			if(leftExpr==null){
				return null;
				//throw new RuntimeException("RelationalExpresion中左值变量表达式为空!");
			}else{
				if(leftExpr.isComplicated()){
					Domain d=vex.getDomain(leftVar);
					SymbolFactor s=SymbolFactor.genSymbol(leftVar.getType(), leftVar.getImage());
					vex.addSymbolDomain(s, d);
					vex.addValue(leftVar, new Expression(s));
				}
			}
		}else {
			SimpleNode operatorNode=(SimpleNode) n.getFirstChildOfType(ASTAssignmentOperator.class);
			if(operatorNode!=null){
				//对条件表达式中包含赋值的情况进行单独处理：if((v=getValue()) > 0)
				SimpleNode leftNode=(SimpleNode) operatorNode.getLastSibling();
				leftVar=resetSymbolExpressionForConditionVariable(leftNode);
			}
		}
		return leftVar;
	}
	
	public Object visit(ASTRelationalExpression node, Object data) {
		ConditionData condata = (ConditionData) data;
		if(node.getOperatorType().size()>1){
			return data;
		}
		String operator=node.getOperatorType().get(0);
		SimpleNode left = (SimpleNode) node.jjtGetChild(0);
		SimpleNode right = (SimpleNode) node.jjtGetChild(1);
		
		//begin: modified by zys 2011.6.20
		VariableNameDeclaration leftVar=resetSymbolExpressionForConditionVariable(left);
		VariableNameDeclaration rightVar=resetSymbolExpressionForConditionVariable(right);
		//end: modified by zys 2011.6.20
		
		Expression rightvalue=null,leftvalue=null;
		ExpressionVistorData expdata = new ExpressionVistorData();
		expdata.sideeffect = false;
		expdata.currentvex = condata.currentvex;
		left.jjtAccept(new ExpressionValueVisitor(), expdata);
		leftvalue=expdata.value;
		expdata.value = null;
		right.jjtAccept(new ExpressionValueVisitor(), expdata);
		rightvalue=expdata.value;
	
		if(leftvalue==null || rightvalue==null)
		{
			return data;
		}
		
		Expression exp=leftvalue.sub(rightvalue);
		
		if(exp.getSingleFactor() instanceof NumberFactor){
			NumberFactor f=(NumberFactor)exp.getSingleFactor();
			Domain may=null,must=null;
			SymbolFactor s=SymbolFactor.genSymbol(CType_BaseType.getBaseType("int"));
			if((f.getDoubleValue()>0 && operator.equals(">"))||//zys:此处的判断条件也有问题
					(f.getDoubleValue()>=0 && operator.equals(">="))||
					(f.getDoubleValue()<0 && operator.equals("<"))||
					(f.getDoubleValue()<=0 && operator.equals("<="))){
				may=Domain.getFullDomainFromType(f.getType());
				must=Domain.getFullDomainFromType(f.getType());
				
				//zys:2010.3.26 	如果条件限定可以满足，则直接取当前变量的域即可
//				may=f.getDomain(node.getCurrentVexNode().getSymDomainset());
//				must=f.getDomain(node.getCurrentVexNode().getSymDomainset());
				condata.addMayDomain(s, may);
				condata.addMustDomain(s, must);	
			}else{//zys:	不一定为空域
				may=IntegerDomain.getEmptyDomain();
				must=IntegerDomain.getEmptyDomain();
				condata.addMayDomain(s, may);
				condata.addMustDomain(s, must);	
			}
			return data;
		}
		//chh  2010.12.8    if(m>n)m,n都未知时无法判断。
		Domain LDomain=leftvalue.getDomain(expdata.currentvex.getSymDomainset());
		Domain RDomain=rightvalue.getDomain(expdata.currentvex.getSymDomainset());
		if(Config.USEUNKNOWN && (LDomain!=null && RDomain!=null && LDomain.isUnknown() && RDomain.isUnknown())){
			return data;
		}
		
		for(Term t:exp.getTerms()){
			Factor f=t.getSingleFactor();
			if(f instanceof SymbolFactor){
				SymbolFactor s=(SymbolFactor)f;
				Expression temp=new Expression(s).sub(exp);
				Domain rightdomain = temp.getDomain(condata.currentvex.getSymDomainset());
				
				if(rightdomain!=null && !rightdomain.isUnknown()){
					CType type=s.getType();
					Domain may=null,must=null;
					Domain leftdomain=s.getDomainWithoutNull(condata.currentvex.getSymDomainset());
										
					IntegerDomain integerdomain=null;
					DoubleDomain doubledomain=null;
					switch (Domain.getDomainTypeFromType(type)){
					case INTEGER:
						integerdomain=Domain.castToIntegerDomain(rightdomain);
						long max = integerdomain.getMax(), min = integerdomain.getMin();
						if(operator.equals(">")){
							may = Domain.intersect(leftdomain,new IntegerDomain(integerdomain.getMin()+1, Long.MAX_VALUE),type);
							condata.addMayDomain(s, may);
							must = Domain.intersect(leftdomain,new IntegerDomain(max != Long.MAX_VALUE ? max+1 : max, Long.MAX_VALUE),type);
							condata.addMustDomain(s, must);
						}else if (operator.equals(">=")) {
							may = Domain.intersect(leftdomain,new IntegerDomain(integerdomain.getMin(), Long.MAX_VALUE),type);
							condata.addMayDomain(s, may);
							must = Domain.intersect(leftdomain,new IntegerDomain(integerdomain.getMax(), Long.MAX_VALUE),type);
							condata.addMustDomain(s, must);
						}else if (operator.equals("<")) {
							may = Domain.intersect(leftdomain,new IntegerDomain(Long.MIN_VALUE,integerdomain.getMax()-1),type);
							condata.addMayDomain(s, may);
							must = Domain.intersect(leftdomain,new IntegerDomain(Long.MIN_VALUE,min != Long.MIN_VALUE ? min-1 : min),type);
							condata.addMustDomain(s, must);
						}else if (operator.equals("<=")) {
							may = Domain.intersect(leftdomain,new IntegerDomain(Long.MIN_VALUE,integerdomain.getMax()),type);
							condata.addMayDomain(s, may);
							must = Domain.intersect(leftdomain,new IntegerDomain(Long.MIN_VALUE,integerdomain.getMin()),type);
							condata.addMustDomain(s, must);
						}else{
							throw new RuntimeException("This is not a legal RelationalExpression");
						}
						break;
					case DOUBLE:
						doubledomain=Domain.castToDoubleDomain(rightdomain);
						if(operator.equals(">")){
							may = Domain.intersect(leftdomain,new DoubleDomain(DoubleMath.nextfp(doubledomain.getMin()), Double.POSITIVE_INFINITY),type);
							condata.addMayDomain(s, may);
							must = Domain.intersect(leftdomain,new DoubleDomain(DoubleMath.nextfp(doubledomain.getMax()), Double.POSITIVE_INFINITY),type);							condata.addMustDomain(s, must);
						}else if (operator.equals(">=")) {
							may = Domain.intersect(leftdomain,new DoubleDomain(doubledomain.getMin(), Double.POSITIVE_INFINITY),type);
							condata.addMayDomain(s, may);
							must = Domain.intersect(leftdomain,new DoubleDomain(doubledomain.getMax(), Double.POSITIVE_INFINITY),type);
							condata.addMustDomain(s, must);
						}else if (operator.equals("<")) {
							may = Domain.intersect(leftdomain,new DoubleDomain(Double.NEGATIVE_INFINITY,DoubleMath.prevfp(doubledomain.getMax())),type);
							condata.addMayDomain(s, may);
							must = Domain.intersect(leftdomain,new DoubleDomain(Double.NEGATIVE_INFINITY,DoubleMath.prevfp(doubledomain.getMin())),type);
							condata.addMustDomain(s, must);
						}else if (operator.equals("<=")) {
							may = Domain.intersect(leftdomain,new DoubleDomain(Double.NEGATIVE_INFINITY,doubledomain.getMax()),type);
							condata.addMayDomain(s, may);
							must = Domain.intersect(leftdomain,new DoubleDomain(Double.NEGATIVE_INFINITY,doubledomain.getMin()),type);
							condata.addMustDomain(s, must);
						}else{
							throw new RuntimeException("This is not a legal RelationalExpression");
						}
						break;
					}
				}
			}
			//处理系数为-1的情况
			f=t.getMinusSingleFactor();
			if(f instanceof SymbolFactor){
				SymbolFactor s=(SymbolFactor)f;
				Expression temp=exp.add(new Expression(s));
				Domain rightdomain = temp.getDomain(condata.currentvex.getSymDomainset());
				
				if(rightdomain!=null && !rightdomain.isUnknown()){
					CType type=s.getType();
					Domain may=null,must=null;
					Domain leftdomain=s.getDomainWithoutNull(condata.currentvex.getSymDomainset());
										
					IntegerDomain integerdomain=null;
					DoubleDomain doubledomain=null;
					
					switch (Domain.getDomainTypeFromType(type)){
					case INTEGER:
						integerdomain=Domain.castToIntegerDomain(rightdomain);
						long max = integerdomain.getMax(), min = integerdomain.getMin();
						if(operator.equals("<")){
							may = Domain.intersect(leftdomain,new IntegerDomain(integerdomain.getMin()+1, Long.MAX_VALUE),type);
							condata.addMayDomain(s, may);
							must = Domain.intersect(leftdomain,new IntegerDomain(max != Long.MAX_VALUE ? max+1 : max, Long.MAX_VALUE),type);
							condata.addMustDomain(s, must);
						}else if (operator.equals("<=")) {
							may = Domain.intersect(leftdomain,new IntegerDomain(integerdomain.getMin(), Long.MAX_VALUE),type);
							condata.addMayDomain(s, may);
							must = Domain.intersect(leftdomain,new IntegerDomain(integerdomain.getMax(), Long.MAX_VALUE),type);
							condata.addMustDomain(s, must);
						}else if (operator.equals(">")) {
							may = Domain.intersect(leftdomain,new IntegerDomain(Long.MIN_VALUE,integerdomain.getMax()-1),type);
							condata.addMayDomain(s, may);
							must = Domain.intersect(leftdomain,new IntegerDomain(Long.MIN_VALUE,min != Long.MIN_VALUE ? min-1 : min),type);
							condata.addMustDomain(s, must);
						}else if (operator.equals(">=")) {
							may = Domain.intersect(leftdomain,new IntegerDomain(Long.MIN_VALUE,integerdomain.getMax()),type);
							condata.addMayDomain(s, may);
							must = Domain.intersect(leftdomain,new IntegerDomain(Long.MIN_VALUE,integerdomain.getMin()),type);
							condata.addMustDomain(s, must);
						}else{
							throw new RuntimeException("This is not a legal RelationalExpression");
						}
						break;
					case DOUBLE:
						doubledomain=Domain.castToDoubleDomain(rightdomain);
						if(operator.equals("<")){
							may = Domain.intersect(leftdomain,new DoubleDomain(DoubleMath.nextfp(doubledomain.getMin()), Double.POSITIVE_INFINITY),type);
							condata.addMayDomain(s, may);
							must = Domain.intersect(leftdomain,new DoubleDomain(DoubleMath.nextfp(doubledomain.getMax()), Double.POSITIVE_INFINITY),type);							condata.addMustDomain(s, must);
						}else if (operator.equals("<=")) {
							may = Domain.intersect(leftdomain,new DoubleDomain(doubledomain.getMin(), Double.POSITIVE_INFINITY),type);
							condata.addMayDomain(s, may);
							must = Domain.intersect(leftdomain,new DoubleDomain(doubledomain.getMax(), Double.POSITIVE_INFINITY),type);
							condata.addMustDomain(s, must);
						}else if (operator.equals(">")) {
							may = Domain.intersect(leftdomain,new DoubleDomain(Double.NEGATIVE_INFINITY,DoubleMath.prevfp(doubledomain.getMax())),type);
							condata.addMayDomain(s, may);
							must = Domain.intersect(leftdomain,new DoubleDomain(Double.NEGATIVE_INFINITY,DoubleMath.prevfp(doubledomain.getMin())),type);
							condata.addMustDomain(s, must);
						}else if (operator.equals(">=")) {
							may = Domain.intersect(leftdomain,new DoubleDomain(Double.NEGATIVE_INFINITY,doubledomain.getMax()),type);
							condata.addMayDomain(s, may);
							must = Domain.intersect(leftdomain,new DoubleDomain(Double.NEGATIVE_INFINITY,doubledomain.getMin()),type);
							condata.addMustDomain(s, must);
						}else{
							throw new RuntimeException("This is not a legal RelationalExpression");
						}
						break;
					}
				}
			}
		}
		return data;
	}
	
	public Object visit(ASTUnaryExpression node, Object data) {
		ConditionData condata = (ConditionData) data;
		
		//add by zhouhb
		 //2010.9.23
		boolean field=Config.Field && node.getVariableDecl()!=null&&!node.getImage().equals("")&&(node.getImage().contains(".")||node.getImage().contains("->"));
		boolean isMulLevelPointer=false;
		if(node.jjtGetChild(0) instanceof ASTUnaryOperator)
		{
			ASTUnaryOperator o=(ASTUnaryOperator)node.jjtGetChild(0);
			String os=o.getOperatorType().get(0);	
			if(os.equals("*"))
			{
				VariableNameDeclaration v=node.getVariableDecl();
				if(v!=null&&v.getType().isPointType()){
					isMulLevelPointer=true;
				}
			}
		}		
		if(field||isMulLevelPointer){
			VariableNameDeclaration v=node.getVariableDecl();
			if(v==null){
				return data;
			}
			Expression exp=condata.currentvex.getValue(v);
			
			//zhouhb 2011.6.15	if(A.p)
			if(exp==null){
				exp=new Expression(SymbolFactor.genSymbol(v.getType(), v.getImage()));
			}
			for(Term t:exp.getTerms()){
				Factor f=t.getSingleFactor();
				if(f instanceof SymbolFactor){
					SymbolFactor s=(SymbolFactor)f;
					Expression temp=new Expression(s).sub(exp);
					Domain rightdomain = temp.getDomain(condata.currentvex.getSymDomainset());
					Domain leftdomain=s.getDomainWithoutNull(condata.currentvex.getSymDomainset());
					CType type=s.getType();
					
					if(rightdomain!=null){
						Domain may=null,must=null;
						may = Domain.intersect(leftdomain, rightdomain, type);
						if (rightdomain.isCanonical()) {
							must = Domain.intersect(leftdomain, rightdomain, type);
						} else {
							must = Domain.getEmptyDomainFromType(type);
						}
						//zys:2010.4.24 if(p)的意义为p!=0
						if(temp.toString().equals("0")){
							may=Domain.inverse(may);
							must=Domain.inverse(must);
						}
						condata.addMayDomain(s, may);
						condata.addMustDomain(s, must);
					}
				}
				//处理系数为-1情况
				f=t.getMinusSingleFactor();
				if(f instanceof SymbolFactor){
					SymbolFactor s=(SymbolFactor)f;
					Expression temp=new Expression(s).add(exp);
					Domain rightdomain = temp.getDomain(condata.currentvex.getSymDomainset());
					Domain leftdomain=s.getDomainWithoutNull(condata.currentvex.getSymDomainset());
					CType type=s.getType();
					
					if(rightdomain!=null){
						Domain may=null,must=null;
						may = Domain.intersect(leftdomain, rightdomain, type);
						if (rightdomain.isCanonical()) {
							must = Domain.intersect(leftdomain, rightdomain, type);
						} else {
							must = Domain.getEmptyDomainFromType(type);
						}
						condata.addMayDomain(s, may);
						condata.addMustDomain(s, must);
					}
				}
			}
			//return data;
		}//end by zhouhb
		
		if(node.jjtGetChild(0) instanceof ASTUnaryOperator){
			ASTUnaryOperator operator=(ASTUnaryOperator)node.jjtGetChild(0);
			String o=operator.getOperatorType().get(0);			
			if(o.equals("!")){
				ConditionData tempdata = new ConditionData(condata.currentvex);
				node.jjtGetChild(1).jjtAccept(this, tempdata);
				SymbolDomainSet may = tempdata.getFalseMayDomainSet();
				SymbolDomainSet must = tempdata.getFalseMustDomainSet();

				condata.addMayDomain(may);
				condata.addMustDomain(must);
				//condata.setDomainsTable(tempdata.getDomainsTable());
				//zys:2010.4.23	将临时条件数据区清空
				tempdata.clearDomains();
			}else if(o.equals("-")){//liuli：对if(-(常数/表达式))的处理				
				ASTUnaryExpression temp = (ASTUnaryExpression)node.jjtGetChild(1);
				ASTPrimaryExpression primary=(ASTPrimaryExpression)temp.getSingleChildofType(ASTPrimaryExpression.class);
				if(primary!=null){
					primary.jjtAccept(this, data);
				}
			}else if(o.equals("*"))
			{
				
				ConditionData tempdata = new ConditionData(condata.currentvex);
				node.jjtGetChild(1).jjtAccept(this, tempdata);
				SymbolDomainSet may = tempdata.getTrueMayDomainSet();
				SymbolDomainSet must = tempdata.getTrueMustDomainSet();

				condata.addMayDomain(may);
				condata.addMustDomain(must);
				tempdata.clearDomains();  
				
				//处理  *p   也是指针的情况
				VariableNameDeclaration v=node.getVariableDecl();
				if(v==null){
					return data;
				}
			}
		}
		else if(!field){
			ASTPrimaryExpression primary=(ASTPrimaryExpression)node.getSingleChildofType(ASTPrimaryExpression.class);
			if(primary!=null){
				primary.jjtAccept(this, data);
			}
		}
		return data;
	}

	public Object visit(ASTPrimaryExpression node, Object data){
		ConditionData condata = (ConditionData) data;
		//chh  增加判断，node还有子节点的话不在这里分析（子节点是ASTConstant除外）
		if(!node.getImage().equals("")&&(node.jjtGetNumChildren()==0||(node.jjtGetNumChildren()==1&&node.jjtGetChild(0) instanceof ASTConstant))){
			//begin: modified by zys 2011.6.20
			//VariableNameDeclaration v=node.getVariableDecl();
			VariableNameDeclaration v=resetSymbolExpressionForConditionVariable(node);
			//end: modified by zys 2011.6.20
			
			if(v==null){
				return data;
			}
			Expression exp=condata.currentvex.getValue(v);
			
			//zys:2010.3.29	if(p)
			if(exp==null){
				exp=new Expression(SymbolFactor.genSymbol(v.getType(), v.getImage()));
			}
			if(exp.getSingleFactor() instanceof NumberFactor){
				NumberFactor f=(NumberFactor)exp.getSingleFactor();
				Domain may=null,must=null;
				SymbolFactor s=SymbolFactor.genSymbol(CType_BaseType.getBaseType("int"));
				if(f.getDoubleValue()==0){
					may=IntegerDomain.getEmptyDomain();
					must=IntegerDomain.getEmptyDomain();
					condata.addMayDomain(s, may);
					condata.addMustDomain(s, must);	
				}else{
					may=IntegerDomain.getFullDomain();
					must=IntegerDomain.getFullDomain();
					condata.addMayDomain(s, may);
					condata.addMustDomain(s, must);	
				}
				return data;
			}
			
			for(Term t:exp.getTerms()){
				Factor f=t.getSingleFactor();
				if(f instanceof SymbolFactor){
					SymbolFactor s=(SymbolFactor)f;
					Expression temp=new Expression(s).sub(exp);
					Domain rightdomain = temp.getDomain(condata.currentvex.getSymDomainset());
					Domain leftdomain=s.getDomainWithoutNull(condata.currentvex.getSymDomainset());
					CType type=s.getType();
					
					if(rightdomain!=null){
						Domain may=null,must=null;
						may = Domain.intersect(leftdomain, rightdomain, type);
						if (rightdomain.isCanonical()) {
							must = Domain.intersect(leftdomain, rightdomain, type);
						} else {
							must = Domain.getEmptyDomainFromType(type);
						}
						//zys:2010.4.24 if(p)的意义为p!=0
						if(temp.toString().equals("0")){
							may=Domain.inverse(may);
							must=Domain.inverse(must);
						}
						condata.addMayDomain(s, may);
						condata.addMustDomain(s, must);
					}
				}
				//处理系数为-1情况
				f=t.getMinusSingleFactor();
				if(f instanceof SymbolFactor){
					SymbolFactor s=(SymbolFactor)f;
					Expression temp=new Expression(s).add(exp);
					Domain rightdomain = temp.getDomain(condata.currentvex.getSymDomainset());
					Domain leftdomain=s.getDomainWithoutNull(condata.currentvex.getSymDomainset());
					CType type=s.getType();
					
					if(rightdomain!=null){
						Domain may=null,must=null;
						may = Domain.intersect(leftdomain, rightdomain, type);
						if (rightdomain.isCanonical()) {
							must = Domain.intersect(leftdomain, rightdomain, type);
						} else {
							must = Domain.getEmptyDomainFromType(type);
						}
						condata.addMayDomain(s, may);
						condata.addMustDomain(s, must);
					}
				}
			}
			return data;
		}else{
			node.childrenAccept(this, data);
		}
		return data;
	}
	//chh  针对if（常数）这种情况，添加了此函数
	public Object visit(ASTConstant node, Object data) {
		ConditionData condata = (ConditionData) data;
			Domain may=null,must=null;
			SymbolFactor s=SymbolFactor.genSymbol(CType_BaseType.getBaseType("int"));
			if(node.getImage().equals("0")){
				may=IntegerDomain.getEmptyDomain();
				must=IntegerDomain.getEmptyDomain();
				condata.addMayDomain(s, may);
				condata.addMustDomain(s, must);	
			}else{
				may=IntegerDomain.getFullDomain();
				must=IntegerDomain.getFullDomain();
				condata.addMayDomain(s, may);
				condata.addMustDomain(s, must);	
			}
		return data;
	}
	//end
}
