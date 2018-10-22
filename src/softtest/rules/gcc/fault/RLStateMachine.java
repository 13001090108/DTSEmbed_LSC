package softtest.rules.gcc.fault;

import java.util.Enumeration;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.ASTArgumentExpressionList;
import softtest.ast.c.ASTDeclarationList;
import softtest.ast.c.ASTPostfixExpression;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTSelectionStatement;
import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.Node;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.Edge;
import softtest.cfg.c.VexNode;
import softtest.domain.c.analysis.ConditionData;
import softtest.domain.c.analysis.SymbolDomainSet;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.PointerDomain;
import softtest.domain.c.interval.PointerValue;
import softtest.domain.c.symbolic.Expression;
import softtest.domain.c.symbolic.SymbolFactor;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.Method;
import softtest.interpro.c.ScopeType;
import softtest.interpro.c.Variable;
import softtest.rules.c.AliasSetForRM;
import softtest.rules.c.BasicStateMachine;
import softtest.rules.c.StateMachineUtils;
import softtest.summary.gcc.fault.MethodMMFeatureVisitor;
import softtest.summary.gcc.fault.MethodRLFeature;
import softtest.summary.gcc.fault.MethodRLFeatureVisitor;
import softtest.summary.gcc.fault.MethodRMFeature;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.Scope;
import softtest.symboltable.c.Search;
import softtest.symboltable.c.SourceFileScope;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.Type.CType_AllocType;
/**
 * 
 * @author 修改 By 
 *
 */
public class RLStateMachine extends BasicStateMachine{
	@Override
	public void registFetureVisitors() {
		super.registFetureVisitors();
		InterContext.addSideEffectVisitor(MethodRLFeatureVisitor.getInstance());
	}
	// 每个fopen产生一个状态机
	public static List<FSMMachineInstance> createRLStateMachines(SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		String xpath=".//Declaration/InitDeclaratorList/InitDeclarator/Initializer/AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression[@Method='true']"+
		"|.//AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression[@Method='true']";
			
		if(!node.getFileName().endsWith(".h"))
		{		
		List evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		
		for (Object snode : evaluationResults) {
			ASTPrimaryExpression post = (ASTPrimaryExpression) snode;
			MethodNameDeclaration methodDecl = StateMachineUtils.getMethodNameDeclaration(post);
			if (methodDecl == null) {
				continue;
			}
			VariableNameDeclaration varDecl = null;

			if (methodDecl.getMethodSummary() == null) {
				continue;
			}
			//xwt：接下来就是我改的
			MethodRLFeature rlFeture =  (MethodRLFeature) methodDecl
			.getMethodSummary().findMethodFeature(MethodRLFeature.class);
			if (rlFeture != null) {
				FSMMachineInstance fsmins = null;
				if(rlFeture.isAllocateAndReturn()){
					varDecl = MethodMMFeatureVisitor.findAssginDeclInQual((SimpleNode)snode);			
					if (varDecl != null && !varDecl.isStatic()) {
						addFSM(methodDecl.getImage(), list, varDecl, rlFeture.getRelatedReleasedMethod(), (SimpleNode)snode, fsm);
					}
				}

				HashMap<Variable, Method> rlFetures = rlFeture.getRLFetures();
				for (Variable variable : rlFetures.keySet()) {
					if (variable.isParam()) {
						Method methodNameDec = rlFetures.get(variable);
						if(methodNameDec == null||methodNameDec.getMtSummmary()==null)
							continue;
						MethodRMFeature rmFeture = (MethodRMFeature) methodNameDec.getMtSummmary().findMethodFeature(MethodRMFeature.class);
						if (rmFeture == null) {
							continue;
						}
						if (rmFeture.getReleaseMethod() != null) {
							int paIndex = variable.getParamIndex();
							SimpleNode tempNode = null;
							tempNode = (SimpleNode)((SimpleNode)snode).getFirstParentOfType(ASTPostfixExpression.class);
							tempNode = (SimpleNode)tempNode.getFirstChildOfType(ASTArgumentExpressionList.class);
							if(tempNode!= null && tempNode.jjtGetNumChildren()> paIndex){
								tempNode = (SimpleNode)tempNode.jjtGetChild(paIndex);
								tempNode = (SimpleNode)tempNode.getFirstChildOfType(ASTUnaryExpression.class);
								varDecl = tempNode.getVariableNameDeclaration();
								if (varDecl instanceof VariableNameDeclaration) 
									addFSM(methodDecl.getImage(), list, varDecl, rmFeture.getReleaseMethod() , (SimpleNode)snode, fsm);
							}
						}
					}
					else if(variable.getScopeType() == ScopeType.INTER_SCOPE ){
						SourceFileScope sfScope = findSourceFileScope(((SimpleNode) snode).getScope());
						VariableNameDeclaration varDecl1 = (VariableNameDeclaration)Search.searchInVariableUpward(variable.getName(), sfScope);
						Method methodNameDec = rlFetures.get(variable);
						if(methodNameDec == null||methodNameDec.getMtSummmary()==null||varDecl1==null)
							continue;
						MethodRMFeature rmFeture = (MethodRMFeature) methodNameDec.getMtSummmary().findMethodFeature(MethodRMFeature.class);
						if (rmFeture.getReleaseMethod() != null){
							addFSM(methodDecl.getImage(), list, varDecl1, rmFeture.getReleaseMethod(), (SimpleNode)snode, fsm);
						}
					}
				}
			}
			else{
				MethodRMFeature rmFeture = (MethodRMFeature) methodDecl
				.getMethodSummary().findMethodFeature(MethodRMFeature.class);
				if (rmFeture == null) {
					continue;
				}
				varDecl = MethodMMFeatureVisitor.findAssginDeclInQual(post);
				if(varDecl==null)
				{
					continue;
				}
				if(varDecl.isParam()){
					continue;
				}else {
					SimpleNode sn=varDecl.getNode();
					if(sn.getFirstParentOfType(ASTDeclarationList.class)!=null)
					{
						continue;
					}
				}

				Method med=rmFeture.getReleaseMethod();
				if(med!=null)
					addFSM(post.getImage(), list, varDecl, med, post, fsm);
			}
		}
		}
		return list;
	 
	}
	
	
	private static void addFSM(String dNamemethodName, List<FSMMachineInstance> list, VariableNameDeclaration varDecl, Method releaseMethod, SimpleNode node, FSMMachine fsm) {
		// 仅对局部变量检测
		if (!varDecl.isParam()) {
			FSMMachineInstance fsminstance = fsm.creatInstance();
			AliasSetForRM alias = new AliasSetForRM();
			fsminstance.setResultString(varDecl.getImage());
			alias.add(varDecl);
			alias.setResouceName("Resource");
			alias.setResource(varDecl.getNode());
			fsminstance.setRelatedObject(alias);
			fsminstance.setStateData(releaseMethod);
			fsminstance.setRelatedASTNode(node);
			fsminstance.setRelatedVariable(varDecl);
			String desp="";
			if(varDecl.getNode()!=null){
				if (dNamemethodName != null) {
					desp="变量"+varDecl.getImage()+"在第"+varDecl.getNode().getBeginLine()+"行定义"+",在第"+node.getBeginLine()+"行使用方法 "+dNamemethodName+"()分配资源";

				}else {
					desp="变量"+varDecl.getImage()+"在第"+varDecl.getNode().getBeginLine()+"行定义"+",在第"+node.getBeginLine()+"行被分配了资源";
				}
			}
			fsminstance.setDesp(desp);
			list.add(fsminstance);
		}
	}
	
	public static boolean checkAllocMethod(List nodes, FSMMachineInstance fsmin) {
		Iterator i = nodes.iterator();
		while (i.hasNext()) {
			SimpleNode o = (SimpleNode)i.next();
			AliasSetForRM alias = (AliasSetForRM) fsmin.getRelatedObject();
			if (fsmin.getRelatedASTNode() == o) {
				VariableNameDeclaration v = findVariableNameDecl(o);
				if (v != null) {
					alias.add(v);
					alias.setIsReleased(false);
				}
				return true;
			}
		}
		return false;
	}
	
	 /**xwt 解决重复分配的问题。目前认为：在分配状态如果遇到再分配，且别名集中元素唯一，则进入error状态*/
	public static boolean checkAllocError(List nodes, FSMMachineInstance fsmin) {
		AliasSetForRM set  = (AliasSetForRM) fsmin.getRelatedObject();
		boolean returnValue = false;
		for (Object o : nodes) {
			SimpleNode snode = ((SimpleNode)o);
			MethodNameDeclaration methodDecl = StateMachineUtils.getMethodNameDeclaration(snode);
			if (methodDecl == null) {
				continue;
			}
			VariableNameDeclaration varDecl = null;

			if (methodDecl.getMethodSummary() == null) {
				continue;
			}
			//xwt：接下来就是我改的
			MethodRLFeature rlFeture =  (MethodRLFeature) methodDecl
			.getMethodSummary().findMethodFeature(MethodRLFeature.class);
			if (rlFeture != null) {
				if(rlFeture.isAllocateAndReturn()){
					varDecl = MethodMMFeatureVisitor.findAssginDeclInQual((SimpleNode)snode);			
					if (varDecl != null && !varDecl.isStatic()) {
						if(varDecl == fsmin.getRelatedVariable() && set.getTable().size() == 1)
							returnValue = true;
					}
				}

				HashMap<Variable, Method> rlFetures = rlFeture.getRLFetures();
				for (Variable variable : rlFetures.keySet()) {
					if (variable.isParam()) {
						Method methodNameDec = rlFetures.get(variable);
						if (methodNameDec == null|| methodNameDec.getMtSummmary()==null) {
							continue;
						}
						MethodRMFeature rmFeture = (MethodRMFeature) methodNameDec.getMtSummmary().findMethodFeature(MethodRMFeature.class);
						if (rmFeture == null) {
							continue;
						}
						if (rmFeture.getReleaseMethod() != null) {
							int paIndex = variable.getParamIndex();
							SimpleNode tempNode = null;
							tempNode = (SimpleNode)((SimpleNode)snode).getFirstParentOfType(ASTPostfixExpression.class);
							tempNode = (SimpleNode)tempNode.getFirstChildOfType(ASTArgumentExpressionList.class);
							if(tempNode!= null && tempNode.jjtGetNumChildren()> paIndex){
								tempNode = (SimpleNode)tempNode.jjtGetChild(paIndex);
								tempNode = (SimpleNode)tempNode.getFirstChildOfType(ASTUnaryExpression.class);
								varDecl = tempNode.getVariableNameDeclaration();
								if (varDecl instanceof VariableNameDeclaration) 
									if(varDecl == fsmin.getRelatedVariable() && set.getTable().size() == 1)
										returnValue = true;
							}
						}
					}
					else if(variable.getScopeType() == ScopeType.INTER_SCOPE ){
						SourceFileScope sfScope = findSourceFileScope(((SimpleNode) snode).getScope());
						VariableNameDeclaration varDecl1 = (VariableNameDeclaration)Search.searchInVariableUpward(variable.getName(), sfScope);
						Method methodNameDec = rlFetures.get(variable);
						if(methodNameDec == null || methodNameDec.getMtSummmary() == null)
							continue;
						MethodRMFeature rmFeture = (MethodRMFeature) methodNameDec.getMtSummmary().findMethodFeature(MethodRMFeature.class);
						if (rmFeture.getReleaseMethod() != null){
							if(varDecl1 == fsmin.getRelatedVariable() && set.getTable().size() == 1)
								returnValue = true;
						}
					}
				}
			}
			else{
				MethodRMFeature rmFeture = (MethodRMFeature) methodDecl
				.getMethodSummary().findMethodFeature(MethodRMFeature.class);
				if (rmFeture == null) {
					continue;
				}
				varDecl = MethodMMFeatureVisitor.findAssginDeclInQual(snode);
				if(varDecl==null)
				{
					continue;
				}
				if(varDecl.isParam()){
					continue;
				}else {
					SimpleNode sn=varDecl.getNode();
					if(sn.getFirstParentOfType(ASTDeclarationList.class)!=null)
					{
						continue;
					}
				}
			    if(varDecl == fsmin.getRelatedVariable() && set.getTable().size() == 1){
			    	fsmin.setDesp(fsmin.getDesp() + "，在第"+snode.getEndLine()+"行重复分配内存会造成资源泄漏");
			    	returnValue = true;
			    }
			}
		}
		if(returnValue == true){
			return true;
		}
		return false;
	}
	

	/**
	 * 确定赋值表达式等式左边的变量，考虑两种情况，一种是变量的声明，一种是变量的赋值
	 * @param snode
	 * @return
	 */
	public static VariableNameDeclaration findVariableNameDecl(SimpleNode snode) {
		return MethodMMFeatureVisitor.findAssginDeclInQual(snode);
	}
	
	public static boolean checkReleaseMethod(List<ASTPrimaryExpression> nodes, FSMMachineInstance fsmin) {
		Iterator<ASTPrimaryExpression> i = nodes.iterator();
		AliasSetForRM alias = (AliasSetForRM) fsmin.getRelatedObject();
		while (i.hasNext()) {
			ASTPrimaryExpression node = i.next();
			MethodNameDeclaration methodDecl = StateMachineUtils.getMethodNameDeclaration(node);
			
			if (methodDecl == null) {
				return false;
			}
			VariableNameDeclaration varDecl = null;
		    if (node instanceof ASTPrimaryExpression) {

				ASTPrimaryExpression pri=(ASTPrimaryExpression)node;
				if(pri.getNextSibling() instanceof ASTArgumentExpressionList)
				{
					ASTArgumentExpressionList pl=(ASTArgumentExpressionList)pri.getNextSibling();
					varDecl = MethodMMFeatureVisitor.getArgDecl(pl, 0);
				}
			}
			if (varDecl != null && alias.getTable().contains(varDecl)) {
				alias.setIsReleased(true);
				return true;
			}
			if(methodDecl.getMethodSummary() == null )
				return false;
			MethodRLFeature rlFeture = (MethodRLFeature) methodDecl.getMethodSummary().findMethodFeature(MethodRLFeature.class);
			if (rlFeture != null) {
				
				HashMap<Variable, Method> rlFetures = rlFeture.getRLFetures();
				for (Variable variable : rlFetures.keySet()) {
					Method methodNameDec = rlFetures.get(variable);
					if(methodNameDec!=null&&methodNameDec.getName().equals(((Method) fsmin.getStateData()).getName())){							
						varDecl = MethodMMFeatureVisitor.findArgDeclInQual(node);
					}
					if(alias.getTable() == null)
							continue;
					if (varDecl!=null&&alias.getTable().contains(varDecl)) {
							alias.setIsReleased(true);
							return true;
					}
				}	
			}
		}
		return false;
	}
	
	public static boolean checkResourceNULL(VexNode vex, FSMMachineInstance fsmin) {
		if(vex.getName().startsWith("return")){
			Hashtable<String, Edge> inEdges = vex.getInedges();
			
			for (String str : inEdges.keySet()) {
				boolean isNull = false;
				Edge edge = inEdges.get(str);
				VexNode pre = edge.getTailNode();
				Domain domain;
				if (pre.getName().startsWith("if_head"))
				{
					domain  = vex.getDomain(fsmin.getRelatedVariable());
					if(domain instanceof PointerDomain)
						if(((PointerDomain)domain).Type.contains(CType_AllocType.Null))
							isNull=true;		
				}
				if(isNull)
					return true;
				
			}
		}
		
		if (vex.getName().startsWith("if_out")) {
			Hashtable<String, Edge> inEdges = vex.getInedges();
			boolean isrl = false;
			for (String str : inEdges.keySet()) {
				Edge edge = inEdges.get(str);
				VexNode pre = edge.getTailNode();
				boolean isNull = false;
				if (isNullPoint(pre, fsmin.getRelatedVariable())) {
					isNull = true;
				} else if (pre.getName().startsWith("if_head")) {
					ConditionData cData = pre.getCondata();
					if(cData == null)
						continue;
					Expression value = pre.getValue(fsmin.getRelatedVariable());
					String eq = "!=";
					if (value!=null&&!isNull&&edge.getName().startsWith("T")) {
						SymbolDomainSet domainSet = cData.getTrueMayDomainSet();
						if (value.getSingleFactor() instanceof SymbolFactor &&
								isNullPoint(domainSet.getDomain((SymbolFactor) value.getSingleFactor()))) {
							isNull = true;
						}
						eq = "==";
					} else if (value!=null&&!isNull&&edge.getName().startsWith("F")) {
						SymbolDomainSet domainSet = cData.getFalseMayDomainSet();
						if (value.getSingleFactor() instanceof SymbolFactor &&
								isNullPoint(domainSet.getDomain((SymbolFactor) value.getSingleFactor()))) {
							isNull = true;
						}
						eq = "!=";
					}
					Method methodDecl = (Method) fsmin.getStateData();
					if (!isNull && methodDecl.getName().equals("close")) {
						SimpleNode ifnode = pre.getTreenode();
						if (ifnode != null) {
							String xpath = ".//EqualityExpression[@Operators = '"+eq+"'][.//UnaryExpression[./UnaryOperator[@Operators = '-']]/UnaryExpression//Constant[@Image = '1']]/UnaryExpression[./PostfixExpression]";
							List<SimpleNode> results = StateMachineUtils.getEvaluationResults((SimpleNode)ifnode.jjtGetChild(0), xpath);
							if(results.size() == 1){
								ASTUnaryExpression ue = (ASTUnaryExpression) results.get(0);
								if (ue.getVariableDecl() == fsmin.getRelatedVariable()) {
									isNull = true;
								}
							}
						}
					}
				}
				FSMMachineInstance prefsmin = pre.getFSMMachineInstanceSet().getTable().get(fsmin);
				if (!isNull) {
					if (prefsmin != null) {
						AliasSetForRM alias2 = (AliasSetForRM) prefsmin
								.getRelatedObject();
						if (!alias2.isReleased()) {
							isrl = true;
						}
					}
				}
			}
			if (!isrl) {
				return true;
			}
		} else {
			// 处理if (***) return;
			isNullPath(fsmin, vex);
		}
		return false;
	}
	
	public static boolean checkReleaseMethod(VexNode vex, FSMMachineInstance fsmin) {
		AliasSetForRM asfm=(AliasSetForRM)fsmin.getRelatedObject();
		if (asfm.getResource().getVariableNameDeclaration().getTypeImage().startsWith("MYSQL")) {
			Node node=vex.getTreenode().getFirstParentOfType(ASTSelectionStatement.class);
			if(node!=null&&node.equals(fsmin.getRelatedASTNode().getFirstParentOfType(ASTSelectionStatement.class))){
				if( asfm.isReleased()){
					return true;
				}
			}
		}else if( asfm.isReleased()){
			return true;
		}
		return false;
	}		
	
	public static boolean checkResourceLeak(VexNode vex, FSMMachineInstance fsmin) {
		AliasSetForRM alias = (AliasSetForRM) fsmin.getRelatedObject();
		VariableNameDeclaration v=fsmin.getRelatedVariable();
		if (alias.getHasReturned()) {
			return false;
		}
		if (isNullPoint(vex, fsmin.getRelatedVariable())
				&& vex.getName().startsWith("return")) {
			return false;
		}
		if (!alias.isEmpty()) {
			return false;
		}
		if (isNullPath(fsmin, vex) && vex.getName().startsWith("return")) {
			return false;
		}
		boolean isrl = false;
		if (vex.getName().startsWith("func_out")
				|| vex.getName().startsWith("return")) {
			AliasSetForRM asf=(AliasSetForRM)fsmin.getRelatedObject();
			if(asf == null ||asf.getResource()==null||asf.getResource().getVariableNameDeclaration()==null)
				return false;
			if(asf.getResource().getVariableNameDeclaration().getTypeImage().startsWith("MYSQL")){
				if(null==vex.getTreenode().getFirstParentOfType(ASTSelectionStatement.class)){
					if (vex.getName().startsWith("return")) {
						if(asf.isReleased()){
							isrl = false;
						}else {
							fsmin.setDesp(fsmin.getDesp() +",在第 "+vex.getTreenode().getEndLine()+ " 行发生资源泄露");
							System.out.println(fsmin.getDesp());
							isrl = true;
						}
					}
				}
			}				
			if (!alias.isReleased()) {
					fsmin.setDesp(fsmin.getDesp() +",在第 "+vex.getTreenode().getEndLine()+ " 行发生资源泄露");
					isrl = true;
			}
			if (isrl){
				return true;
			}
			else
				return false;
		}
		return false;
	}	
	
	private static boolean isNullPath(FSMMachineInstance fsmin, VexNode vex) {
		Method methodDecl = (Method) fsmin.getStateData();
		if (methodDecl.getName().equals("close")) {
			Hashtable<String, Edge> inEdges = vex.getInedges();
			if (inEdges.size() == 1) {
				Edge edge = inEdges.elements().nextElement();
				VexNode pre = edge.getTailNode();
				if (pre.getName().startsWith("if_head")) {
					String eq;
					if (edge.getName().startsWith("T")) {
						eq = "==";
					} else if (edge.getName().startsWith("F")) {
						eq = "!=";
					} else {
						return false;
					}
					SimpleNode ifnode = pre.getTreenode();
					if (ifnode == null) {
						return false;
					}
					String xpath = ".//EqualityExpression[@Operators = '"+eq+"'][.//UnaryExpression[./UnaryOperator[@Operators = '-']]/UnaryExpression//Constant[@Image = '1']]/UnaryExpression[./PostfixExpression]";
					List<SimpleNode> results = StateMachineUtils.getEvaluationResults((SimpleNode)ifnode.jjtGetChild(0), xpath);
					if(results.size() == 1){
						ASTUnaryExpression ue = (ASTUnaryExpression) results.get(0);
						if (ue.getVariableDecl() == fsmin.getRelatedVariable()) {

							AliasSetForRM alias2 = (AliasSetForRM) fsmin.getRelatedObject();
							alias2.setIsReleased(true);
							return true;
						}
					}
				}
			}
		}
		return false;
	}
	public static boolean checkReassigned(List nodes, FSMMachineInstance fsmin) {
		Iterator i = nodes.iterator();
		AliasSetForRM alias = (AliasSetForRM) fsmin.getRelatedObject();
		Hashtable<VariableNameDeclaration, VariableNameDeclaration> tables=alias.getTable();
		List<Variable> varList=new LinkedList<Variable>();
		Enumeration<VariableNameDeclaration> key=tables.keys();
		while(key.hasMoreElements())
		{
			varList.add(Variable.getVariable(key.nextElement()));
		}
		while (i.hasNext()) {
			ASTPrimaryExpression pe = (ASTPrimaryExpression)i.next();
			MethodNameDeclaration methodDecl = StateMachineUtils.getMethodNameDeclaration(pe);
			if (methodDecl == null) {
				continue;
			}

			if (methodDecl.getMethodSummary() == null) {
				continue;
			}
			MethodRLFeature vgaFeture = (MethodRLFeature) methodDecl
					.getMethodSummary().findMethodFeature(MethodRLFeature.class);
			if (vgaFeture == null) {
				return false;
			}
			HashMap<Variable, String> vgaMap=vgaFeture.getAllDesp();
			Iterator<Variable>iter=vgaMap.keySet().iterator();
			while (iter.hasNext()) {
				Variable var=iter.next();
				if(varList.contains(var)){
					fsmin.setDesp(fsmin.getDesp() +",在第 "+pe.getBeginLine()+ "行通过全局变量"+var.getName()+"的赋值导致发生资源泄露");
					return true;
				}
			}
		}
		return false;
	}
	
	
	private static boolean isNullPoint(VexNode vexNode, VariableNameDeclaration v) {
		
		if (vexNode.getDomain(v) instanceof PointerDomain && !Domain.isEmpty(((PointerDomain)vexNode.getDomain(v)))) {
			PointerDomain domain = (PointerDomain) vexNode.getDomain(v);
			if(domain.getValue()==PointerValue.NULL)
			{
				return true;
			}
			
		}
		return false;
	}
	
	private static boolean isNullPoint(Domain domain) {
		if (domain instanceof PointerDomain && !domain.isUnknown()) {
			PointerDomain pDomain = (PointerDomain) domain;
			if (!pDomain.Type.contains(CType_AllocType.NotNull)) {
				return true;
			}
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
