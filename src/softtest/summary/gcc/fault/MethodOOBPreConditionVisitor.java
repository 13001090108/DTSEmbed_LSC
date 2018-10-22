package softtest.summary.gcc.fault;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import softtest.ast.c.*;
import softtest.cfg.c.VexNode;
import softtest.domain.c.analysis.ExpressionValueVisitor;
import softtest.domain.c.analysis.ExpressionVistorData;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.IntegerDomain;
import softtest.domain.c.interval.IntegerInterval;
import softtest.domain.c.symbolic.Expression;
import softtest.domain.c.symbolic.Power;
import softtest.domain.c.symbolic.Term;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.Variable;
import softtest.rules.c.StateMachineUtils;
import softtest.rules.gcc.fault.OOB_CheckStateMachine;
import softtest.summary.c.MethodFeatureVisitor;
import softtest.summary.c.MethodSummary;
import softtest.summary.gcc.fault.MethodOOBPreCondition;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.NameDeclaration;
import softtest.symboltable.c.NameOccurrence;
import softtest.symboltable.c.Scope;
import softtest.symboltable.c.Search;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.Type.CType_Array;
import softtest.symboltable.c.Type.CType_Pointer;
import softtest.symboltable.c.SourceFileScope;

/**
 * 数组越界的前置条件访问者
 * @author zys	  modified by chh
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
		if (node.jjtGetNumChildren() == 1 || !node.getOperators().contains("[")) 
		{
			return super.visit(node, data);
		}
		
		//取得数组名,并查找数组声明位置获取其长度（维数）
		//modified by nmh
		VariableNameDeclaration array = null;
		if( node.getOperators().contains(".") || node.getOperators().contains("->") )
		{	
			ASTPostfixExpression postExp = (ASTPostfixExpression)node;								
			NameDeclaration decl = null;
			decl = postExp.getVariableDecl();			
			//处理数组下标是非常量的情况dongyk
			if(decl==null&&postExp.getImage().indexOf("[exp")>=0)
			{
				String image=postExp.getImage();
				image=image.substring(0, image.indexOf("[exp"));
				if (!image.equals("")) {
					Scope scope = postExp.getScope();
					decl = Search.searchInVariableUpward(image, scope);					
				}
			}
			if (decl instanceof VariableNameDeclaration) {ArrayList<Boolean> flags=postExp.getFlags();
			ArrayList<String> operators=postExp.getOperatorType();
			Scope localScope = postExp.getScope();
			int operatorIndex=0;
			for(int i=0;i<flags.size();i++){
				String operator=operators.get(flags.size()-i-1);
				if(operator.equals("[")){
					String image=postExp.getImage();
					operatorIndex=image.indexOf("[", operatorIndex);
					if(operatorIndex>0)
					{							
						image=image.substring(0, operatorIndex);
						operatorIndex++;
						NameDeclaration decl1=Search.searchInVariableAndMethodUpward(image, localScope);							
						if(decl1!=null && (decl1.getType() instanceof CType_Array)){
			        		array=(VariableNameDeclaration)decl1;	
			        		break;
			        	}	
					}	
				}
		        		
		}
			if(array==null)
			array = (VariableNameDeclaration) decl;
	}
	}
	else
	{
		ASTPrimaryExpression priExpr=(ASTPrimaryExpression) node.jjtGetChild(0);	
		array=priExpr.getVariableNameDeclaration();
	}

		


		
		//获取数组的每一维下标
		int num=node.jjtGetNumChildren();
		
		if(array==null || !(array.getType() instanceof CType_Array)){
			return super.visit(node, data);		
		}

		CType_Array temp = (CType_Array) array.getType();
		
		for(int i=1;i<num;i++)
		{	
			if(!(node.jjtGetChild(i) instanceof ASTExpression))
				continue;
			ASTExpression expNode = (ASTExpression) node.jjtGetChild(i);
			
			long length=temp.getDimSize();
			if(temp.getOriginaltype() instanceof CType_Array)
				temp=(CType_Array) temp.getOriginaltype();
			
			//modified by nmh
			// 
			
			
			if(expNode.getSingleChildofType(ASTPrimaryExpression.class) != null)
			{//数组下标为单个变量，如a[i]
				ASTPrimaryExpression subExpr=(ASTPrimaryExpression) expNode.getSingleChildofType(ASTPrimaryExpression.class);
				VariableNameDeclaration subScript=subExpr.getVariableNameDeclaration();
				if(length!=-1&&length!=0)
					confirmOOBVar(new IntegerInterval(0,length-1), subScript, (MethodOOBPreCondition) data, node,0, -1);
			}
			else if(expNode.getSingleChildofType(ASTPostfixExpression.class) != null)
			{//数组下标为a[s.i]复杂结构体类型
				ASTPostfixExpression subExpr=(ASTPostfixExpression) expNode.getSingleChildofType(ASTPostfixExpression.class);
				ASTPrimaryExpression priExpr = null;
				NameDeclaration decl = null, primDecl = null;
				VariableNameDeclaration subScript = null;
				if(subExpr.jjtGetChild(0) instanceof ASTPrimaryExpression)
				{
					priExpr = (ASTPrimaryExpression)subExpr.jjtGetChild(0);
					primDecl = priExpr.getVariableDecl();
				}
				if(priExpr == null)
					return super.visit(node, data);
				if (primDecl != null && primDecl instanceof VariableNameDeclaration) {
					/*mems 标识结构体变量出现顺序，用于结构体初始化变量识别*/
					ArrayList<VariableNameDeclaration> memlist = ((VariableNameDeclaration)primDecl).mems;
					int index = -1;//如果是结构体成员变量，按照结构体定义的顺序，计算出是结构体的第几个成员
        			if(memlist != null)
        			{
        				decl = subExpr.getVariableDecl();
        				if (decl instanceof VariableNameDeclaration) {
        					subScript = (VariableNameDeclaration) decl;
        				    for(int j = 0; j < memlist.size(); j++)
        				    	if((memlist.get(j)).equals(subScript))
        				    	{
        				    		index = j;
        				    		break;
        				    	}
        			   }
				    }
        			if(length!=-1&&length!=0)
        				if(((VariableNameDeclaration)primDecl).isParam())
        					confirmOOBVar(new IntegerInterval(0,length-1), (VariableNameDeclaration)primDecl, (MethodOOBPreCondition) data, node,0,index);			
        				else
        					confirmOOBVar(new IntegerInterval(0,length-1), subScript, (MethodOOBPreCondition) data, node,0,-1);
				}
			}				
			else{
				//数组下标为常数或复杂表达式，如 a[i*j],这种情况暂时不处理
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
	 * 如果是局部变量，则通过relationwith函数判断局部变量的值是否和全局或参数变量相关，相关则生成前置条件；
	 */
	/*
	* modified by nmh
	* 增加一个参数flag
	* 如果已知的区间要比所约束的区间大，则flag = 0
	* 如果已知的区间要比所约束的区间小，则flag = 1
	* 
	* 增加一个参数idx
	* 如果是结构体成员变量，标志出是结构体的第几个成员
	*/
	private void confirmOOBVar(IntegerInterval integerInterval,VariableNameDeclaration varDecl,MethodOOBPreCondition feature, SimpleNode node, int flag, int idx) 
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
		////可由OOB_Check检测的函数不再生成或传递摘要
		if(((ASTExpression)node.getFirstChildInstanceofType(ASTExpression.class))!=null&&
				((ASTExpression)node.getFirstChildInstanceofType(ASTExpression.class)).getSingleChildofType(ASTPrimaryExpression.class)!=null&&
				((ASTPrimaryExpression)((ASTExpression)node.getFirstChildInstanceofType(ASTExpression.class)).getSingleChildofType(ASTPrimaryExpression.class)).jjtGetNumChildren()==0)  {
			ASTPrimaryExpression  pnode =  (ASTPrimaryExpression)((ASTExpression)node.getFirstChildInstanceofType(ASTExpression.class)).getSingleChildofType(ASTPrimaryExpression.class);
			Object[] res = OOB_CheckStateMachine.ableToCheck((ASTPrimaryExpression)pnode,varDecl);
	         if(res[0].toString()=="true" && res[1]!=null){//判断是否可check
	           	if(OOB_CheckStateMachine.checkOOB((ASTPrimaryExpression)res[1],integerInterval,varDecl))//判断是否OOB
	           		return;
	        }	
		}
		if(node.getFirstParentOfType(ASTLogicalANDExpression.class)!=null)
			return;
		String desp = "函数" + methodDecl.getImage() + "("+methodDecl.getFileName()+")"+";它在文件第"+node.getBeginLine()+"行使用了变量"+varDecl.getImage()+"可能导致数组越界";
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
							String tempT = t.toString();
							tempT = tempT.replaceAll("\\.[0]*","");
							if(tempT.contains("."))
								return;
							if(t.getOperator()=="+") 
								offset-=Integer.parseInt(tempT);
							else if(t.getOperator()=="-") 
								offset+=Integer.parseInt(tempT);
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
											if(p.getOperator()=="*") {
												String tempP = p.toString();
												tempP = tempP.replaceAll("\\.[0]*","");
												if(tempP.contains("."))
													return;
												else
													times*=Integer.parseInt(tempP);
											}
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
			feature.addSubScriptVariable(var, integerInterval, desp, flag,idx);
		}
	}

	/*摘要向上传递，添加摘要*/
	private void confirmOOBVar(IntegerInterval summaryInterval, VariableNameDeclaration varDecl, SimpleNode node, String oldDesp, MethodOOBPreCondition feature, int flag,int idx) {
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
		//可由OOB_Check检测的函数不再生成或传递摘要
		if(node.jjtGetParent()!=null&&
				node.jjtGetParent() instanceof ASTPostfixExpression&&
				((ASTArgumentExpressionList)((ASTPostfixExpression)node.jjtGetParent()).getFirstChildInstanceofType(ASTArgumentExpressionList.class))!=null&&
				((ASTArgumentExpressionList)((ASTPostfixExpression)node.jjtGetParent()).getFirstChildInstanceofType(ASTArgumentExpressionList.class)).getSingleChildofType(ASTPrimaryExpression.class)!=null&&
				((ASTPrimaryExpression)((ASTArgumentExpressionList)((ASTPostfixExpression)node.jjtGetParent()).getFirstChildInstanceofType(ASTArgumentExpressionList.class)).getSingleChildofType(ASTPrimaryExpression.class)).jjtGetNumChildren()==0)  {
			ASTPrimaryExpression  pnode =  (ASTPrimaryExpression)((ASTArgumentExpressionList)((ASTPostfixExpression)node.jjtGetParent()).getFirstChildInstanceofType(ASTArgumentExpressionList.class)).getSingleChildofType(ASTPrimaryExpression.class);
			if(!pnode.isMethod()){
				Object[] res = OOB_CheckStateMachine.ableToCheck((ASTPrimaryExpression)pnode,varDecl);
		         if(res[0].toString()=="true" && res[1]!=null){//判断是否可check
		           	if(OOB_CheckStateMachine.checkOOB((ASTPrimaryExpression)res[1],summaryInterval,varDecl))//判断是否OOB
		           		return;
		        }	
			}
		}
		if(node.getFirstParentOfType(ASTLogicalANDExpression.class)!=null)
			return;
		String desp = "函数" + methodDecl.getImage() +"("+ methodDecl.getFileName()+");它在文件第"+node.getBeginLine()+"行调用了"+oldDesp;
		
		if (varDecl!=null&&(varDecl.isParam() || varDecl.getScope() instanceof SourceFileScope||relationvar!=null)) 
		{
			VexNode vex=node.getCurrentVexNode();
			Domain d=vex.getVarDomainSet().getDomain(varDecl);
			if(d!=null && !Domain.isEmpty(d)
					&&!(Domain.castToIntegerDomain(d).getMax()==Long.MAX_VALUE&&Domain.castToIntegerDomain(d).getMin()==Long.MIN_VALUE)
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
							String tempT = t.toString();
							tempT = tempT.replaceAll("\\.[0]*","");
							if(tempT.contains("."))
								return;
							if(t.getOperator()=="+") 
								offset-=Integer.parseInt(tempT);
							else if(t.getOperator()=="-") 
								offset+=Integer.parseInt(tempT);
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
										 	if(p.getOperator()=="*") {
												String tempP = p.toString();
												tempP = tempP.replaceAll("\\.[0]*","");
												if(tempP.contains("."))
													return;
												else
													times*=Integer.parseInt(tempP);
											}
											else 
												return;
										}
								 }
							}
						}
					}
					summaryInterval=new IntegerInterval(summaryInterval.getMin(),(summaryInterval.getMax()+offset)/times);
					
				}
			feature.addSubScriptVariable(var, summaryInterval, desp, flag,idx);
		}
	}
	
	private IntegerInterval getNewInterval(IntegerInterval x, IntegerInterval y) {
		long xMax = x.getMax(), yMax = y.getMax();
		
		return xMax > yMax ? new IntegerInterval(0, yMax) : new IntegerInterval(0, xMax);
	}
	
	/**计算被调用函数的前置条件是否需要向上层函数传递 */
	private void calSummaryTransmit(ASTPrimaryExpression node, MethodOOBPreCondition feature) {
		MethodNameDeclaration mnd=node.getMethodDecl();
		if(mnd!=null){
			MethodSummary summary=mnd.getMethodSummary();
			if(mnd!=null){
			    summary=mnd.getMethodSummary();
			}
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
							if(index!=-1 && node.getNextSibling()!= null)
							{//目前只考虑简单的函数调用如f(10) f(i)，暂时未考虑f(i+j)
								ASTAssignmentExpression assignExpr=(ASTAssignmentExpression) node.getNextSibling().jjtGetChild(index);
								ASTPrimaryExpression priExpr=(ASTPrimaryExpression) assignExpr.getSingleChildofType(ASTPrimaryExpression.class);
								if(priExpr!=null)
								{
									VariableNameDeclaration varDecl=priExpr.getVariableNameDeclaration();
									confirmOOBVar(preCondition.getSubScriptInterval(subScriptVar), varDecl, node, preCondition.getSubScriptDesp(subScriptVar), feature,preCondition.getSubScriptFlag(subScriptVar),preCondition.getSubScriptIndex(subScriptVar));
								}
							}
						} else {
							//如果是全局变量调用
							NameDeclaration nd=Search.searchInVariableUpward(subScriptVar.getName(),node.getScope());
							if(nd instanceof VariableNameDeclaration)
							{
								confirmOOBVar(preCondition.getSubScriptInterval(subScriptVar), (VariableNameDeclaration)nd, node, preCondition.getSubScriptDesp(subScriptVar), feature, preCondition.getSubScriptFlag(subScriptVar),preCondition.getSubScriptIndex(subScriptVar));
							}
						}
					}
				}
			}
		}
	}
	
	/*
	 * add by nmh
	 * 对于数组未知，但是偏移已知的情况，添加函数摘要
	 */
	@Override
	public Object visit(ASTUnaryExpression node, Object data) {
		// *(ptr + i),目前只考虑i为已知的
		if (node.jjtGetNumChildren() != 2) {
			return super.visit(node, data);
		}
		if (!(node.jjtGetChild(0) instanceof ASTUnaryOperator) || !node.getImage().equals("*")) {
			return super.visit(node, data);
		}
		
		//目前只考虑偏移已知的情况
		String xpath = "/UnaryExpression/PostfixExpression/PrimaryExpression/Expression/AssignmentExpression/AdditiveExpression[.//Constant]";
		List<SimpleNode> addNodeList = StateMachineUtils.getEvaluationResults(node, xpath);
		for (SimpleNode addNode : addNodeList) {
			int index = -1;
			VariableNameDeclaration varDecl = null;
			IntegerInterval retInterval = null;
			
			int childrenNum = addNode.jjtGetNumChildren();		
			for (int i = 0; i < childrenNum; ++i) {
				SimpleNode pmNode = (SimpleNode) addNode.jjtGetChild(i);
				String xPath = "./PostfixExpression[count(*)=1]/PrimaryExpression"; //排除int ns[]; ns[0] += ns[0] + 8;
				List<SimpleNode > primExpNodeList = StateMachineUtils.getEvaluationResults(pmNode, xPath);
				if (primExpNodeList == null || primExpNodeList.size() == 0) {
					continue;
				}
				
				ASTPrimaryExpression primExpNode = (ASTPrimaryExpression) primExpNodeList.get(0);
				NameDeclaration nameDecl = primExpNode.getVariableDecl();
				if (!(nameDecl instanceof VariableNameDeclaration)) {
					continue;
				}
				
				varDecl = (VariableNameDeclaration) nameDecl;
				if (varDecl.getType() instanceof CType_Pointer || varDecl.getType() instanceof CType_Array) {
					index = i;
					break;
				}
			}
			if( index == -1 )
				return super.visit(node, data);
			
			VexNode vex = addNode.getCurrentVexNode();
			Domain domain = vex.getDomain(varDecl);
        	if(domain!= null && domain.isUnknown())
        	{
        		ExpressionValueVisitor expVisitor = new ExpressionValueVisitor();
    			retInterval = new IntegerInterval(0, 0); //初始化retInterval的区间
    			String operator = null;
    			ArrayList<String>opes = addNode.getOperatorType();
    			int size = opes.size();
    			if(size != childrenNum - 1 )
    				return super.visit(node, data);
    			for (int m = 0, i = 0; m < childrenNum; ++m) {
    				if (m == index) {
    					continue;
    				}
    				operator = opes.get(i);
    				SimpleNode pmNode = (SimpleNode) addNode.jjtGetChild(m);
    				ExpressionVistorData domainData = new ExpressionVistorData();
    				domainData.currentvex = pmNode.getCurrentVexNode();
    				pmNode.jjtAccept(expVisitor, domainData);
    				Expression value1 = domainData.value;
					Domain mydomain=null;
					if(value1!=null)
					    mydomain = value1.getDomain(domainData.currentvex.getSymDomainset());
					
    				if (domainData != null && mydomain != null && !mydomain.isUnknown() && mydomain instanceof IntegerDomain) {
    					IntegerDomain iDomain = (IntegerDomain) mydomain;
    					IntegerInterval tmpInter = iDomain.jointoOneInterval();
    					
    					if (operator.equals("+")) {
    						retInterval = IntegerInterval.add(retInterval, tmpInter);
    					} else if (operator.equals("-")) {
    						retInterval = IntegerInterval.sub(retInterval, tmpInter);
    					}
    				}
    			}
    			confirmOOBVar(retInterval, varDecl,(MethodOOBPreCondition) data,node,1, -1);
        	}      	
		}
		return super.visit(node, data);
	}
}

