package softtest.rules.gcc.fault;

import java.util.Enumeration;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import softtest.ast.c.ASTArgumentExpressionList;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.VexNode;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.IntegerDomain;
import softtest.domain.c.interval.PointerDomain;
import softtest.domain.c.interval.PointerValue;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.Variable;
import softtest.rules.c.AliasSetForRM;
import softtest.rules.c.BasicStateMachine;
import softtest.rules.c.StateMachineUtils;
import softtest.summary.gcc.fault.MethodMMFeatureVisitor;
import softtest.summary.gcc.fault.MethodRLFeature;
import softtest.summary.gcc.fault.MethodRLFeatureVisitor;
import softtest.summary.gcc.fault.MethodRMFeature;
import softtest.symboltable.c.ClassScope;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.SourceFileScope;
import softtest.symboltable.c.VariableNameDeclaration;
/**
 * 
 * @author 修改 By 
 *
 */
public class RL_PREStateMachine extends BasicStateMachine{
	@Override
	public void registFetureVisitors() {
		super.registFetureVisitors();
		InterContext.addPreConditionVisitor(MethodRLFeatureVisitor.getInstance());
	}
	// 每个fopen产生一个状态机
	public static List<FSMMachineInstance> createRL_PREStateMachines(SimpleNode node, FSMMachine fsm) {
		
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		String xpath=".//Declaration/InitDeclaratorList/InitDeclarator/Initializer/AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression[@Method='true']"+
		"|.//Expression/AssignmentExpression/AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression[@Method='true']";
		
			
		List evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		
		Set<VariableNameDeclaration> varset = new HashSet<VariableNameDeclaration>();
		

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
			addFSM(post.getImage(), list, varDecl, /*rmFeture.getReleaseMethod(),*/ post, fsm);
		}
	
		return list;
	}
	
	
	private static void addFSM(String dNamemethodName, List<FSMMachineInstance> list, VariableNameDeclaration varDecl,/* MethodNameDeclaration releaseMethod,*/ SimpleNode node, FSMMachine fsm) {
		// 仅对局部变量检测
		if (!varDecl.isParam() /*&& !(varDecl.getScope() instanceof SourceFileScope)*/ && !(varDecl.getScope() instanceof ClassScope)) {
			FSMMachineInstance fsminstance = fsm.creatInstance();
			AliasSetForRM alias = new AliasSetForRM();
			fsminstance.setResultString(varDecl.getImage());
			alias.add(varDecl);
			alias.setResouceName("Resource");
			alias.setResource(varDecl.getNode());
			fsminstance.setRelatedObject(alias);
//			fsminstance.setStateData(releaseMethod);
			fsminstance.setRelatedASTNode(node);
			fsminstance.setRelatedVariable(varDecl);
			String desp="";
			
			if (dNamemethodName != null) {
				desp="变量"+varDecl.getImage()+"在第"+varDecl.getNode().getBeginLine()+"行定义"+",在第"+node.getBeginLine()+"行使用方法 "+dNamemethodName+"()分配资源";
				
			}else {
				desp="变量"+varDecl.getImage()+"在第"+varDecl.getNode().getBeginLine()+"行定义"+",在第"+node.getBeginLine()+"行被分配了内存";
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
			
			if (methodDecl == null ||!methodDecl.equals(fsmin.getStateData())) {
				return false;
			}
			VariableNameDeclaration varDecl = null;
		/*	if (node instanceof ASTDeclarator) {
				varDecl = MethodMMFeatureVisitor.findArgDeclInQual(node);
			} else*/ if (node instanceof ASTPrimaryExpression) {
				/*if(methodDecl.getImage().equals("ReleaseDC")) {
					//add by suntao ReleaseDC释放第二个参数
					varDecl = MethodMMFeatureVisitor.getArgDecl((ASTParameterList)node, 1);
				} else {*/
				ASTPrimaryExpression pri=(ASTPrimaryExpression)node;
				if(pri.getNextSibling() instanceof ASTArgumentExpressionList)
				{
					ASTArgumentExpressionList pl=(ASTArgumentExpressionList)pri.getNextSibling();
					varDecl = MethodMMFeatureVisitor.getArgDecl(pl, 0);
				}
					//}
			}
			if (varDecl != null && alias.getTable().contains(varDecl)) {
				alias.setIsReleased(true);
				return true;
			}
		}
		return false;
	}
	
	public static boolean checkResourceNULL(VexNode vex, FSMMachineInstance fsmin) {
		if (vex.getName().startsWith("if_out")&&isNullPoint(vex, fsmin.getRelatedVariable(), fsmin)) {
			return true;
		} else if (vex.getName().startsWith("return")&&isNullPoint(vex, fsmin.getRelatedVariable(), fsmin)) {
			return true;
		} else {
			if(vex.getName().startsWith("func_out")||vex.getName().startsWith("return"))
			{
				if(fsmin.getRelatedVariable().getScope() instanceof SourceFileScope){
					return true;
				}
			}
			return false;
		}
	}
	
	public static boolean checkReleaseMethod(VexNode vex, FSMMachineInstance fsmin) {
		AliasSetForRM asfm=(AliasSetForRM)fsmin.getRelatedObject();
		if( asfm.isReleased())
		{
			return true;
		}
		return false;
		
		/*
		if(vex.getName().startsWith("if_"))
		{
			return false;
		}
		SimpleNode node=vex.getTreenode();
		List<ASTPrimaryExpression >list=node.findXpath(".//AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression[@Method='true']");
		if(list==null||list.size()<1)
		{
			return false;
		}else {
			MethodNameDeclaration methodDecl = (MethodNameDeclaration)fsmin.getStateData();
			Iterator<ASTPrimaryExpression> iter=list.iterator();
	out: while(iter.hasNext())
			{
				ASTPrimaryExpression ape=iter.next();
				if(ape.getImage().equals(methodDecl.getImage()))
				{
					if(ape.getNextSibling()instanceof ASTArgumentExpressionList){
						ASTArgumentExpressionList ael=(ASTArgumentExpressionList)ape.getNextSibling();
						
						List<ASTPrimaryExpression > pList=ael.findXpath(".//AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression[@Method='false']");
						Iterator<ASTPrimaryExpression> initer=pList.iterator();
						while(initer.hasNext()){
							ASTPrimaryExpression pExpression=initer.next();
							VariableNameDeclaration var=StateMachineUtils.getVarDeclaration(pExpression	);
							if(var==fsmin.getRelatedVariable())
							{
								AliasSetForRM alias = (AliasSetForRM) fsmin.getRelatedObject();
								alias.setIsReleased(true);
								alias.remove(var);
								break out;
							}
						}
					}
				}
			}
		}
		
		return false;
	*/
		
	
	
	}
	
//	private static boolean isNullPath(FSMMachineInstance fsmin, VexNode vex) {
//		MethodNameDeclaration methodDecl = (MethodNameDeclaration)fsmin.getStateData();
//		if (/*methodDecl.getImage().equals("closesocket")*/methodDecl.getImage().equals("fclose")) {
//			
//			SimpleNode sNode=vex.getTreenode();
//			ASTSelectionStatement ss=(ASTSelectionStatement)sNode.getFirstParentOfType(ASTSelectionStatement.class);
//			if(ss!=null){
//				ASTEqualityExpression equalityExpression=(ASTEqualityExpression)ss.getFirstChildInstanceofType(ASTEqualityExpression.class);
//				
//				if(equalityExpression!=null&&equalityExpression.getOperators().equals("=="))
//				{
//					List jumpList=sNode.findXpath(".//JumpStatement");
//					if(jumpList.size()>0)
//					{
//						return true;
//					}
//				}
//			}	
//		}
//		return false;
//	}
	
	public static boolean checkResourceLeak(VexNode vex, FSMMachineInstance fsmin) {
		AliasSetForRM alias = (AliasSetForRM) fsmin.getRelatedObject();
		VariableNameDeclaration v=fsmin.getRelatedVariable();
		if (alias.getHasReturned()) {
			return false;
		}
//		if (alias.getTable().size()==0) {
//			return false;
//		}
//		if (alias.isReleased()) {
//			return false;
//		}
		if (!alias.isEmpty()) {
			return false;
		}
		
		// 特殊处理指针分配失败出口处，避免误报
//		if (isNullPoint(vex, fsmin.getRelatedVariable(), fsmin)
//				&& vex.getName().startsWith("return")) {
//			return false;
//		}
		if (vex.getName().startsWith("func_out")
				|| vex.getName().startsWith("return")) {
			if (vex.getDomain(v) instanceof PointerDomain
					&& !Domain.isEmpty(((PointerDomain) vex.getDomain(v)))) {
				
				PointerDomain domain = (PointerDomain) vex.getDomain(v);
				if (domain.getValue() != PointerValue.NULL&&!alias.isReleased()) {
					fsmin.setDesp(fsmin.getDesp() +",在第 "+vex.getTreenode().getBeginLine()+ " 行发生资源泄露");
					return true;
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
	
	
	public static boolean checkReassignedForOperator(List nodes, FSMMachineInstance fsmin) {
		Iterator i = nodes.iterator();
		AliasSetForRM alias = (AliasSetForRM) fsmin.getRelatedObject();
		Hashtable<VariableNameDeclaration, VariableNameDeclaration> tables=alias.getTable();
		List<VariableNameDeclaration>varList2=new LinkedList<VariableNameDeclaration>();
		Enumeration<VariableNameDeclaration> key=tables.keys();
		while(key.hasMoreElements()){
			varList2.add(key.nextElement());
		}
		while (i.hasNext()) {
			ASTPrimaryExpression pe = (ASTPrimaryExpression)i.next();
			if(pe.getBeginLine()==fsmin.getRelatedASTNode().getBeginLine())
			{
				continue;
			}
			VariableNameDeclaration vnd=MethodMMFeatureVisitor.findAssginDeclInQual(pe);
			if(vnd==null)
			{
				continue;
			}
			if(varList2.contains(vnd)){
				fsmin.setDesp(fsmin.getDesp() +",在第 "+pe.getBeginLine()+ "行通过变量"+vnd.getImage()+"的赋值导致发生资源泄露");
				
				return true;
			}
		}
		return false;
	}
	
	
	private static boolean isNullPoint(VexNode vexNode, VariableNameDeclaration v,FSMMachineInstance fsmin) {
		
		if (vexNode.getDomain(v) instanceof PointerDomain && !Domain.isEmpty(((PointerDomain)vexNode.getDomain(v)))) {
			PointerDomain domain = (PointerDomain) vexNode.getDomain(v);
			if(domain.getValue()==PointerValue.NULL)
			{
				return true;
			}
			

//			SimpleNode sNode=vexNode.getTreenode();
//			if(sNode.getFirstParentOfType(ASTSelectionStatement.class)!=null)
//			{
//				ASTSelectionStatement ce=(ASTSelectionStatement)sNode.getFirstParentOfType(ASTSelectionStatement.class);
//				ASTEqualityExpression equalityExpression=(ASTEqualityExpression)ce.getFirstChildInstanceofType(ASTEqualityExpression.class);
//				
//				if(equalityExpression!=null&&equalityExpression.getOperators().equals("==")){
//					List eqList=equalityExpression.findXpath(".//UnaryExpression/PostfixExpression/PrimaryExpression");
//					if(eqList.size()>0)
//					{
//						ASTPrimaryExpression astPri=(ASTPrimaryExpression)eqList.get(0);
//						if(fsmin.getRelatedVariable().equals(astPri.getVariableNameDeclaration()))
//							return true;
//					}
//					
//				}
//			}
		
//			if (domain.isCanonical() /*&& domain.range.isIn(0)*/) {
//				return true;
//			}
		}
		return false;
	}
	
}
