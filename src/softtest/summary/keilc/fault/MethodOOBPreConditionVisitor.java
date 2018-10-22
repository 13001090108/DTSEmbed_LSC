package softtest.summary.keilc.fault;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTExpression;
import softtest.ast.c.ASTFunctionDefinition;
import softtest.ast.c.ASTPostfixExpression;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.CParserVisitorAdapter;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.VexNode;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.IntegerDomain;
import softtest.domain.c.interval.IntegerInterval;
import softtest.domain.c.symbolic.Expression;
import softtest.domain.c.symbolic.Power;
import softtest.domain.c.symbolic.Term;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.Variable;
import softtest.rules.c.StateMachineUtils;
import softtest.summary.c.MethodFeatureVisitor;
import softtest.summary.c.MethodSummary;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.NameDeclaration;
import softtest.symboltable.c.NameOccurrence;
import softtest.symboltable.c.Scope;
import softtest.symboltable.c.Search;
import softtest.symboltable.c.SourceFileScope;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.Type.CType_Array;

/**
 * 数组越界的前置条件访问者
 * @author zys	
 * 2010-5-12
 */
public class MethodOOBPreConditionVisitor extends CParserVisitorAdapter implements MethodFeatureVisitor {

	private static MethodOOBPreConditionVisitor instance = null;
	private MethodNameDeclaration methodDecl = null;
	
	private MethodOOBPreConditionVisitor() {
	}
	
	public static MethodFeatureVisitor getInstance() {
		if (instance == null) {
			instance = new MethodOOBPreConditionVisitor();
		}
		return instance;
	}
	
	public void visit(VexNode vexNode) {
		SimpleNode node = vexNode.getTreenode();
		if (node == null) {
			return;
		}
		
		MethodOOBPreCondition feature = new MethodOOBPreCondition();
		
		methodDecl = InterContext.getMethodDecl(vexNode);
		if (methodDecl != null) {
			node.jjtAccept(instance, feature);
		}
		if (feature.isSubScriptMapEmpty()) {
			return;
		}
		
		MethodSummary mtSummary = InterContext.getMethodSummary(vexNode);
		if (mtSummary != null) {
			mtSummary.addPreCondition(feature);
		}
	}
	
	/** 如果主函数内部存在函数调用节点，则查看是否需要将被调用函数的前置条件进行传递*/
	public Object visit(ASTPrimaryExpression node, Object data)
	{
		if(node.isMethod())
		{
			calSummaryTransmit(node, (MethodOOBPreCondition) data);
		}
		return super.visit(node, data);
	}

	/** 在函数内部查找所有使用变量作为数组下标的节点，计算是否需要为该函数生成该下标变量的前置条件*/
	public Object visit(ASTPostfixExpression node, Object data)
	{
		if (node.jjtGetNumChildren() == 1 || !node.getOperators().startsWith("[")) 
		{
			return super.visit(node, data);
		}
		
		//取得数组名,并查找数组声明位置获取其长度（维数）
		ASTPrimaryExpression priExpr=(ASTPrimaryExpression) node.jjtGetChild(0);
		VariableNameDeclaration array=priExpr.getVariableNameDeclaration();
		
		//获取数组的每一维下标
		int num=node.jjtGetNumChildren();
		//liuli
		if(array!= null && !(array.getType() instanceof CType_Array)){
			return super.visit(node, data);		
		}

		CType_Array temp = (CType_Array) array.getType();
		
		for(int i=1;i<num;i++)
		{	//liuli
			if(!(node.jjtGetChild(i) instanceof ASTExpression))
				continue;
			ASTExpression expNode = (ASTExpression) node.jjtGetChild(i);
			ASTPrimaryExpression subExpr=(ASTPrimaryExpression) expNode.getSingleChildofType(ASTPrimaryExpression.class);
			long length=temp.getDimSize();
			if(temp.getOriginaltype() instanceof CType_Array)
				temp=(CType_Array) temp.getOriginaltype();
			if(subExpr!=null)
			{//数组下标为单个变量，如a[i]
				VariableNameDeclaration subScript=subExpr.getVariableNameDeclaration();
				confirmOOBVar(new IntegerInterval(0,length-1), subScript, i-1, (MethodOOBPreCondition) data, node);
			}else{
				//数组下标为常数或复杂表达式，如a[10] a[i*j],这种情况暂时不处理
				
			}
		}
		return super.visit(node, data);
	}
	/**
	 * chh   对于如果将全局变量或者函数参数赋值给函数内的局部变量后将此变量作为数组下标使用，那么应该返回涉及的全局
	 * 和参数变量，以便生成前置条件的函数摘要。(目前只能处理在对局部变量的赋值中使用了单个全局变量或单个函数参数的情况)
	 */
	private VariableNameDeclaration relationwith(VariableNameDeclaration varDecl, SimpleNode node)
	{
		List<VariableNameDeclaration> varlist=new  LinkedList<VariableNameDeclaration>();
		// 将全局变量添加到varlist中
		Scope scope =methodDecl.getScope();
		Map<VariableNameDeclaration, ArrayList<NameOccurrence>> varOccs = scope.getVariableDeclarations();
		Iterator it=varOccs.keySet().iterator();
		VariableNameDeclaration key;
		while(it.hasNext())
		{ 
			key=(VariableNameDeclaration)it.next();
			if(key.getScope() instanceof SourceFileScope)
			varlist.add(key);
		}
		SimpleNode decNode=methodDecl.getMethodNameDeclaratorNode();
		if(decNode instanceof ASTFunctionDefinition)
		{
			String xpath=".//ParameterList/ParameterDeclaration/Declarator/DirectDeclarator";
			List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(decNode, xpath);
			Iterator<SimpleNode> itr = evaluationResults.iterator();
			while(itr.hasNext()) {
				SimpleNode snode = itr.next();
				VariableNameDeclaration parvar=snode.getVariableNameDeclaration();
				varlist.add(parvar);
			}
		}
		VexNode vex=node.getCurrentVexNode();
		Expression leftvalue=new Expression(0);
		if(vex!=null&&varDecl!=null)leftvalue=vex.getValue(varDecl);
		ArrayList<Term> list=new ArrayList<Term>();
		if(leftvalue!=null)
		list=leftvalue.getTerms();
		int _num=0;
		for(Term t:list){
			for(VariableNameDeclaration var:varlist){
				if(t.toString().contains(var.getImage()+"_"))
					{
						_num++;
						if(_num>1)return null;
						else return var;
					}
			}
		}
		return null;
	}
	/**
	 * 检查数组声明或使用时的下标变量，如果该变量为函数参数或全局变量，则为该函数生成该数组下标的前置条件；
	 * 如果为函数参数，同时获取该参数所在函数列表中的位置（index）
	 * 
	 * 如果是局部变量，则不生成前置条件；
	 */
	private void confirmOOBVar(IntegerInterval integerInterval,VariableNameDeclaration varDecl, int index,MethodOOBPreCondition feature, SimpleNode node) 
	{
		
		Variable var=null;
		VariableNameDeclaration relationvar=null;
		if(varDecl!=null&&(varDecl.isParam() || varDecl.getScope() instanceof SourceFileScope))
		var= Variable.getVariable(varDecl);
		//将全局变量或参数赋给局部变量后，使用局部变量作为数组下标，这些全局变量或参数也应该生成前置条件
		else if(relationwith(varDecl,node)!=null)
		{
			relationvar=relationwith(varDecl,node);
			var=Variable.getVariable(relationwith(varDecl,node));
		}
		if (var == null) 
		{
			return;
		}
		
		String desp = "函数" + methodDecl.getImage() + ";它在文件第"+node.getBeginLine()+"行使用了变量"+varDecl.getImage()+"可能导致数组越界";
		/** 仅处理函数参数、或者全局变量,如果是形参，则同时求得其index */
		if (varDecl!=null&&(varDecl.isParam() || varDecl.getScope() instanceof SourceFileScope||relationvar!=null)) 
		{
			VexNode vex=node.getCurrentVexNode();
			Domain d=vex.getVarDomainSet().getDomain(varDecl);
			if(d!=null && !Domain.isEmpty(d)&&!d.equals(new IntegerDomain(new IntegerInterval())) && !(d.isUnknown()))
			{//如果下标变量的区间已知，则不再生成函数摘要，而是在模式计算中进行检测
				return;
			}
			if (feature.containsSubScriptVar(var)) {
				integerInterval = getNewInterval(feature.getSubScriptInterval(var), integerInterval);
			}
			//chh 如果i的值经过加减乘除运算，并且该值还与传参相关，需要重新计算i的可取值范围; 
			//chh  例：i=i*k+k（k=4）i作为size为20的数组下标时取值范围为0-3
			Expression leftvalue=vex.getValue(varDecl);
			if(leftvalue!=null&&leftvalue.toString().contains("_"))
				{
				int offset=0,times=1,_num=0;	
				ArrayList<Term> list=leftvalue.getTerms();
					for(Term t:list)
					{
						if(!t.toString().contains("_"))
						{
							if(t.getOperator()=="+") 
								offset-=Integer.parseInt(t.toString());
							else if(t.getOperator()=="-") 
								offset+=Integer.parseInt(t.toString());
							else 
								return ;
						}
						else {
							_num++;
							if(_num>1||(!t.toString().contains(varDecl.getImage()+"_")&&(relationvar!=null&&!t.toString().contains(relationvar.getImage()+"_"))))
								return ;
							else 
							{
								 ArrayList<Power> listp=t.getPowers();
								 for(Power p:listp)
								 {
									 if(!p.toString().contains("_"))
										{
											if(p.getOperator()=="*") 
												times*=Integer.parseInt(p.toString());
											else 
												return;
										}
								 }
							}
						}
					}
					integerInterval=new IntegerInterval((integerInterval.getMin()+offset)/times,(integerInterval.getMax()+offset)/times);
					
				}
			//end  
			feature.addSubScriptVariable(var, integerInterval, desp);
		}
	}

	private void confirmOOBVar(IntegerInterval summaryInterval, VariableNameDeclaration varDecl, SimpleNode node, String oldDesp, MethodOOBPreCondition feature) {
		Variable var=null;
		VariableNameDeclaration relationvar=null;
		if(varDecl!=null&&(varDecl.isParam() || varDecl.getScope() instanceof SourceFileScope))
		var= Variable.getVariable(varDecl);
		//将全局变量或参数赋给局部变量后，使用局部变量作为数组下标，这些全局变量或参数也应该生成前置条件
		else if(relationwith(varDecl,node)!=null)
		{
			relationvar=relationwith(varDecl,node);
			var=Variable.getVariable(relationwith(varDecl,node));
		}
		
		String desp = "函数" + methodDecl.getImage() + ";它在文件第"+node.getBeginLine()+"行调用了"+oldDesp;
		
		if (varDecl!=null&&(varDecl.isParam() || varDecl.getScope() instanceof SourceFileScope||relationvar!=null)) 
		{
			VexNode vex=node.getCurrentVexNode();
			Domain d=vex.getVarDomainSet().getDomain(varDecl);
			if(d!=null && !Domain.isEmpty(d)&&!(Domain.castToIntegerDomain(d).getMax()==Long.MAX_VALUE&&Domain.castToIntegerDomain(d).getMin()==Long.MIN_VALUE)
					&&!(d.isUnknown()))
			{
				//如果下标变量的区间已知，则不再生成函数摘要，而是在模式计算中进行检测
				return;
			}
			if (feature.containsSubScriptVar(var)) {
				summaryInterval = getNewInterval(feature.getSubScriptInterval(var), summaryInterval);
			}
			//chh 如果i的值经过加减乘除运算，并且该值还与传参相关，需要重新计算i的可取值范围; 
			//chh  例：i=i*k+k（k=4）i作为size为20的数组下标时取值范围为0-3
			Expression leftvalue=vex.getValue(varDecl);
			if(leftvalue!=null&&leftvalue.toString().contains("_"))
				{
				int offset=0,times=1,_num=0;	
				ArrayList<Term> list=leftvalue.getTerms();
					for(Term t:list)
					{
						if(!t.toString().contains("_"))
						{
							if(t.getOperator()=="+") 
								offset-=Integer.parseInt(t.toString());
							else if(t.getOperator()=="-") 
								offset+=Integer.parseInt(t.toString());
							else 
								return ;
						}
						else {
							_num++;
							if(_num>1||(!t.toString().contains(varDecl.getImage()+"_")&&(relationvar!=null&&!t.toString().contains(relationvar.getImage()+"_"))))
								return ;
							else 
							{
								 ArrayList<Power> listp=t.getPowers();
								 for(Power p:listp)
								 {
									 if(!p.toString().contains("_"))
										{
											if(p.getOperator()=="*") 
												times*=Integer.parseInt(p.toString());
											else 
												return;
										}
								 }
							}
						}
					}
					summaryInterval=new IntegerInterval(summaryInterval.getMin(),(summaryInterval.getMax()+offset)/times);
					
				}
			feature.addSubScriptVariable(var, summaryInterval, desp);
		}
	}
	
	private IntegerInterval getNewInterval(IntegerInterval x, IntegerInterval y) {
		long xMax = x.getMax(), yMax = y.getMax();
		
		return xMax > yMax ? new IntegerInterval(0, yMax) : new IntegerInterval(0, xMax);
	}
	
	/**计算被调用函数的前置条件是否需要向上层函数传递 */
	private void calSummaryTransmit(ASTPrimaryExpression node, MethodOOBPreCondition feature) {
		MethodNameDeclaration mnd=node.getMethodDecl();
		MethodSummary summary = null;
		if(mnd != null)//xwt:临时解决方案
		summary = mnd.getMethodSummary();
		if(summary!=null)
		{
			MethodOOBPreCondition preCondition = (MethodOOBPreCondition) summary.findMethodFeature(MethodOOBPreCondition.class);
			if(preCondition!=null)
			{
				Set<Variable> subScriptVarSet = preCondition.getSubScriptVariableSet();
				for (Variable subScriptVar : subScriptVarSet) {
					if (subScriptVar.isParam()) {
						//如果是函数参数调用,则找到相应位置的实参
						int index=subScriptVar.getParamIndex();
						if(index!=-1)
						{//目前只考虑简单的函数调用如f(10) f(i)，暂时未考虑f(i+j)
							ASTAssignmentExpression assignExpr=(ASTAssignmentExpression) node.getNextSibling().jjtGetChild(index);
							ASTPrimaryExpression priExpr=(ASTPrimaryExpression) assignExpr.getSingleChildofType(ASTPrimaryExpression.class);
							if(priExpr!=null)
							{
								VariableNameDeclaration varDecl=priExpr.getVariableNameDeclaration();
								confirmOOBVar(preCondition.getSubScriptInterval(subScriptVar), varDecl, node, preCondition.getSubScriptDesp(subScriptVar), feature);
							}
						}
					} else {
						//如果是全局变量调用
						NameDeclaration nd=Search.searchInVariableUpward(subScriptVar.getName(),node.getScope());
						if(nd instanceof VariableNameDeclaration)
						{
							confirmOOBVar(preCondition.getSubScriptInterval(subScriptVar), (VariableNameDeclaration)nd, node, preCondition.getSubScriptDesp(subScriptVar), feature);
						}
					}
				}
			}
		}
	}
}

