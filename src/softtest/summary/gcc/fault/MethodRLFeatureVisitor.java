package softtest.summary.gcc.fault;

import java.util.HashMap;
import java.util.List;

import softtest.ast.c.ASTArgumentExpressionList;
import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTCompoundStatement;
import softtest.ast.c.ASTPostfixExpression;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTSelectionStatement;
import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.CParserVisitorAdapter;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.VexNode;
import softtest.config.c.Config;
import softtest.domain.c.analysis.ExpressionValueVisitor;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.Method;
import softtest.interpro.c.ScopeType;
import softtest.interpro.c.Variable;
import softtest.rules.c.StateMachineUtils;
import softtest.summary.c.MethodFeature;
import softtest.summary.c.MethodFeatureVisitor;
import softtest.summary.c.MethodSummary;
import softtest.symboltable.c.ClassScope;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.NameDeclaration;
import softtest.symboltable.c.Scope;
import softtest.symboltable.c.Search;
import softtest.symboltable.c.SourceFileScope;
import softtest.symboltable.c.VariableNameDeclaration;

public class MethodRLFeatureVisitor extends CParserVisitorAdapter implements MethodFeatureVisitor {
	class RLInfo {
		public RLInfo(String traceinfo, int startline,Method methodName) {
			this.traceinfo = traceinfo;
			this.startline = startline;
			this.methodName = methodName;
		}
		String traceinfo;
		int startline;
		Method methodName;
	}
	
	private final static String RM_FUNC_XPATH = ".//AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression[@Method='true']";
	private static MethodRLFeatureVisitor instance;
	
	private MethodRLFeatureVisitor(){	
	}
	
	public static MethodRLFeatureVisitor getInstance(){
		if(instance==null){
			instance=new MethodRLFeatureVisitor();
		}
		return instance;
	}
	private MethodNameDeclaration methodDecl = null;
	
	public void visit(VexNode vexNode) {
		MethodRLFeature rlFeature=new MethodRLFeature();
		SimpleNode treeNode=vexNode.getTreenode();
		if(treeNode==null) {
			return;
		}
		methodDecl = InterContext.getMethodDecl(vexNode);
		treeNode.jjtAccept(instance, rlFeature);
	
		// 将计算出的函数特性添加到函数摘要中
		MethodSummary summary = InterContext.getMethodSummary(vexNode);
		if (summary != null && !rlFeature.isEmpty()) {
			summary.addSideEffect(rlFeature);
			if (Config.INTER_METHOD_TRACE) {
				if (methodDecl != null) {
					System.err.println(methodDecl.getFullName() + " " + rlFeature);
				}
			}
		}
	}
	
	/**
	 * 查找C当前函数中调用的资源申请
	 * 由于是函数摘要，只记录跟函数外部作用域的变量，包括成员，全局以及函数参数变量
	 * @param node
	 * @param allocs
	 */
	private boolean findRAlloc_Func(SimpleNode node, HashMap<VariableNameDeclaration, RLInfo> allocs){
		List<SimpleNode> result = StateMachineUtils.getEvaluationResults(node, RM_FUNC_XPATH);
		if (result.size() == 0) {
			return false;
		}
		for (SimpleNode methodNode: result) {
			MethodNameDeclaration methodDecl = StateMachineUtils.getMethodNameDeclaration(methodNode);
			if (methodDecl == null) {
				continue;
			}
			VariableNameDeclaration varDecl = null;
			if (methodDecl.getMethodSummary() == null) {
				continue;
			}
			MethodRMFeature rmFeture = (MethodRMFeature)methodDecl.getMethodSummary().findMethodFeature(MethodRMFeature.class);
			if (rmFeture == null) {
				MethodRLFeature rlFeture = (MethodRLFeature)methodDecl.getMethodSummary().findMethodFeature(MethodRLFeature.class);
				if(rlFeture == null)
					continue;
				if(rlFeture.isAllocateAndReturn()){
				    varDecl = MethodMMFeatureVisitor.findAssginDeclInQualWithPointer(methodNode);
				    if (varDecl != null) { 
					    allocs.put(varDecl, new RLInfo(null, methodNode.getBeginLine(),rlFeture.getAllocMethod()));				
				    }
				}
				HashMap<Variable, Method> rlFetures = rlFeture.getRLFetures();
				for (Variable variable : rlFetures.keySet()){
					if (variable.isParam()) {
						Method methodNameDec = rlFetures.get(variable);
						if(methodNameDec == null)
							continue;
						
						int paIndex = variable.getParamIndex();
						SimpleNode tempNode = null;
						tempNode = (SimpleNode)((SimpleNode)methodNode).getFirstParentOfType(ASTPostfixExpression.class);
						tempNode = (SimpleNode)tempNode.getFirstChildOfType(ASTArgumentExpressionList.class);
						if(tempNode!= null && tempNode.jjtGetNumChildren()> paIndex){
							tempNode = (SimpleNode)tempNode.jjtGetChild(paIndex);
							tempNode = (SimpleNode)tempNode.getFirstChildOfType(ASTUnaryExpression.class);
							varDecl = tempNode.getVariableNameDeclaration();
							allocs.put(varDecl, new RLInfo(null, methodNode.getBeginLine(),methodNameDec));
							//从这里开始
						}
					}
					else if(variable.getScopeType() == ScopeType.INTER_SCOPE ){
							SourceFileScope sfScope = findSourceFileScope(((SimpleNode) methodNode).getScope());
							VariableNameDeclaration varDecl1 = (VariableNameDeclaration)Search.searchInVariableUpward(variable.getName(), sfScope);
							Method methodNameDec1 = rlFetures.get(variable);
							if(methodNameDec1 != null)
								allocs.put(varDecl1, new RLInfo(null, methodNode.getBeginLine(),methodNameDec1));
					}			
				}
			}
			else if (rmFeture.getReleaseMethod() != null){
				varDecl = MethodMMFeatureVisitor.findAssginDeclInQualWithPointer(methodNode);
				if (varDecl != null) {
					allocs.put(varDecl, new RLInfo(null, methodNode.getBeginLine(),methodDecl.getMethod()));
				}
			}			
		}
		if(allocs.size()>0)
			return true;
		else return false;
	}
	
	/**
	 * 查找C当前函数中调用的资源释放
	 * 如果已经函数中已经有申请了此变量的，将申请的map中对应去掉
	 * 由于是函数摘要，只记录跟函数外部作用域的变量，包括成员，全局以及函数参数变量
	 * @param node
	 * @param allocs
	 * @param releas
	 */
	private boolean findRRelease_Func(SimpleNode node, HashMap<VariableNameDeclaration, RLInfo> allocs,HashMap<VariableNameDeclaration, RLInfo> releas){
		List<SimpleNode> result = StateMachineUtils.getEvaluationResults(node, RM_FUNC_XPATH);
		if (result.size() == 0) {
			return false;
		}
		for (SimpleNode methodNode: result) {
			MethodNameDeclaration methodDecl = StateMachineUtils.getMethodNameDeclaration(methodNode);
			if (methodDecl == null) {
				continue;
			}
			VariableNameDeclaration varDecl = null;
			/*xwt：反正现在就这么几个函数，直接硬写得了，省的搞函数特征了*/
			if (methodDecl.getImage().equals("fclose")||methodDecl.getImage().equals("mysql_close")
					||methodDecl.getImage().equals("close")) {
				varDecl = MethodMMFeatureVisitor.findArgDeclInQual(methodNode);
				if (varDecl != null)
				{
					if(methodNode.getCurrentVexNode()== null)
						continue;
					VexNode  releaseVex = methodNode.getCurrentVexNode();
					if(releaseVex.getContradict())
						continue;
					SimpleNode selectSta = (SimpleNode) methodNode.getFirstParentOfType(ASTSelectionStatement.class); // 改
			        /*zhb回来以后问问问问问问问问 
					if (selectSta != null){
						selectSta = (SimpleNode)selectSta.jjtGetChild(0).jjtGetChild(0);
						ConditionData condition = selectSta.getCurrentVexNode().getCondata();
						if(condition == null)
							continue;
						if(condition.getDomainsTable() == null)
							continue;
						if(condition.getDomainsTable().size()!=1)
							continue;
						VariableNameDeclaration var = condition.getDomainsTable().keys().nextElement();
						if(var == null)
							continue;		
						SimpleNode temp = getVariableNode(methodNode);
						if(temp == null)
							continue;
						if(!varDecl.equals(var))
							continue;
						if(allocs.containsKey(varDecl))
							allocs.remove(varDecl);
						else 
							releas.put(varDecl, new RLInfo(null, methodNode.getBeginLine(),methodDecl));
					}
					else {
						SimpleNode temp = getVariableNode(methodNode);
						if(temp == null)
							continue;
						if(allocs.containsKey(varDecl))
							allocs.remove(varDecl);
						else 
							releas.put(varDecl, new RLInfo(null, methodNode.getBeginLine(),methodDecl));
					}*/
					if(allocs.containsKey(varDecl))
						allocs.remove(varDecl);
					else 
						releas.put(varDecl, new RLInfo(null, methodNode.getBeginLine(),methodDecl.getMethod()));
				}
			}
		}
		if(releas.size()>0)
			return true;
		else return false;
	}
	
	private boolean findGlobalVar(SimpleNode node, HashMap<VariableNameDeclaration, RLInfo> releas){
		String xpath = ".//Expression/AssignmentExpression[count(*)=3 and ./AssignmentOperator";
		List<SimpleNode> result = StateMachineUtils.getEvaluationResults(node, xpath);
		if (result.size() == 0) {
			return false;
		}
		for (SimpleNode varNode: result) {
			if(!(varNode.jjtGetChild(0) instanceof ASTUnaryExpression))
				continue;
			if(!(varNode.jjtGetChild(2) instanceof ASTAssignmentExpression))
				continue;
			ASTUnaryExpression p = (ASTUnaryExpression) varNode.jjtGetChild(0);
			VariableNameDeclaration leftvar = p.getVariableDecl();
			if(leftvar == null)
			    continue;
		    if(leftvar!=null && !(leftvar.getScope() instanceof SourceFileScope))
			    continue;
		    if(varNode.jjtGetChild(2) instanceof ASTAssignmentExpression){
		    	ASTAssignmentExpression a = (ASTAssignmentExpression) varNode.jjtGetChild(2);
			    ASTUnaryExpression un = (ASTUnaryExpression) a.getFirstChildOfType(ASTUnaryExpression.class);
			    if(un == null)
				    continue;
			    VariableNameDeclaration rightvar = un.getVariableDecl();
			    if(rightvar!=null){
			    	releas.put(rightvar, new RLInfo(null, un.getBeginLine(), null));
		            return true;
		        }		    
		    }
		}
		return false;
	}
	
	public Object visit(ASTCompoundStatement node,Object feature){
		
		MethodRLFeature rlfeature = null;
		if (feature instanceof MethodRLFeature)
		{
			rlfeature = (MethodRLFeature) feature;
		}
		HashMap<VariableNameDeclaration, RLInfo> allocs = new HashMap<VariableNameDeclaration, RLInfo>();
		HashMap<VariableNameDeclaration, RLInfo> releas = new HashMap<VariableNameDeclaration, RLInfo>();
		
		boolean found1 = findRAlloc_Func(node, allocs);
		boolean found2 = findRRelease_Func(node,allocs,releas);
		boolean found3 = findGlobalVar(node,releas);
		
		if (!found1 && !found2 && !found3)
		{
			return null;
		}
		String xpath = ".//jump_statement[@Image='return']/expression";
		List<SimpleNode> returnExps = StateMachineUtils.getEvaluationResults(node, xpath);
		VariableNameDeclaration re = null;
		for (SimpleNode rExp : returnExps) {
			List temp = rExp.findChildrenOfType(ASTUnaryExpression.class);
			if (temp != null && temp.size() > 0)
			{
				ASTUnaryExpression pnode = (ASTUnaryExpression) temp.get(0);
				re = pnode.getVariableDecl();
			}
			if (re instanceof VariableNameDeclaration && allocs.containsKey(re)){
				rlfeature.setAllocateAndReturn(true);
				rlfeature.setAllocMethod(allocs.get(re).methodName);
				MethodRMFeature rmFeture = (MethodRMFeature)allocs.get(re).methodName.getMtSummmary().findMethodFeature(MethodRMFeature.class);
				if(rmFeture!=null){
					Method med = rmFeture.getReleaseMethod();
				    NameDeclaration relMethodName=Search.searchInVariableAndMethodUpward(med.getReturnType().getName(), node.getScope());
				    if(relMethodName!=null&&relMethodName instanceof MethodNameDeclaration)
				        rlfeature.setRelatedReleasedMethod(((MethodNameDeclaration) relMethodName).getMethod());
				}
				String trace = "resourse is allocated on line " + rExp.getBeginLine() + " in function \"" + methodDecl.getImage() + "\"";
				if (Config.DTS_LANGUAGE == Config.LANG_CHINESE) {
					trace = "函数" +methodDecl.getImage() + "在第" + rExp.getBeginLine() + "行分配资源";
				}
				if (allocs.get(re).traceinfo != null) {
					trace += ", " + allocs.get(re).traceinfo;
				}
				rlfeature.setRetTrace(trace);
			}
		}
		// 将最后结果添加到函数副作用的摘要中
		for (VariableNameDeclaration varDecl : allocs.keySet()) {
			Variable variable = Variable.getVariable(varDecl);
			if (variable != null) {
				if (!isInterVar(varDecl)) {
					continue;
				}
				rlfeature.addVariable(variable, allocs.get(varDecl).methodName);
				String trace = "resourse is allocated on line " + allocs.get(varDecl).startline + " in function \"" + methodDecl.getImage() + "\"";
				if (Config.DTS_LANGUAGE == Config.LANG_CHINESE) {
					trace = "函数" +methodDecl.getImage() + "在第" + allocs.get(varDecl).startline + "行分配资源";
				}
				if (allocs.get(varDecl).traceinfo != null) {
					trace += ", " + allocs.get(varDecl).traceinfo;
				}
				rlfeature.addDesp(variable, trace);
				rlfeature.setRetTrace(trace);
			}
		}
		for (VariableNameDeclaration varDecl : releas.keySet()) {			
			Variable variable = Variable.getVariable(varDecl);
			if (variable != null) {
				rlfeature.addVariable(variable, releas.get(varDecl).methodName);
				String trace = "Resource is released " + releas.get(varDecl).startline + " in function \"" + methodDecl.getImage() + "\"";
				if (Config.DTS_LANGUAGE == Config.LANG_CHINESE) {
					trace = "函数" +methodDecl.getImage() + "在第" + releas.get(varDecl).startline + "行释放资源";
				}
				if (releas.get(varDecl).traceinfo != null) {
					trace += ", " + releas.get(varDecl).traceinfo;
				}
				rlfeature.addDesp(variable, trace);
				rlfeature.setRetTrace(trace);
			}
		}
		return node.childrenAccept(this, feature);
	}
	
	public Object visit(ASTPrimaryExpression node,Object data){
		MethodRLFeature feature = (MethodRLFeature)data;
		if(node.isMethod() && node.getMethodDecl() != null) {
			MethodNameDeclaration methodDecl = (MethodNameDeclaration) node.getMethodDecl();
			MethodSummary mtSummary = methodDecl.getMethodSummary();
			if(mtSummary != null) {		
				for(MethodFeature mFeature : mtSummary.getSideEffects()) {
					if(mFeature instanceof MethodRLFeature) {	
						MethodRLFeature rlFeature = (MethodRLFeature) mFeature;	
						for(Variable variable : rlFeature.getRLVariable()) {								
							if(variable != null&&feature.isContain(variable)) {//若当前函数已有此变量后置信息，不再记录
								String trace = rlFeature.getDesp(variable);
								if (Config.DTS_LANGUAGE == Config.LANG_CHINESE) {
									trace =trace + node.getFileName() + " on line "  + node.getBeginLine() + " in function \"" + methodDecl.getImage();
								}

								if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
									trace =trace + "在文件 " + node.getFileName() +" 第" + node.getBeginLine() + "函数"+ methodDecl.getImage();
								}

								feature.addDesp(variable, trace);
								feature.setRetTrace(trace);
							}
						}
					}
				}
			}
		}
		return null;
	}
	
	
	/** 判断是否是参数或成员变量或全局变量*/
	private boolean isInterVar(VariableNameDeclaration vnd) {
		if (vnd.getScope() == null) {
			return true;
		}
		if (vnd.isParam() || vnd.getScope() instanceof ClassScope || vnd.getScope() instanceof SourceFileScope){
			return true;
		}
		return false;
	}
   
	private static SourceFileScope findSourceFileScope(Scope scope)
	{
		Scope parent = scope;	
		while(parent!=null && !(parent instanceof SourceFileScope))
		{
			parent = parent.getParent();
		}
		return (SourceFileScope)parent;
	}
	
	
}
