package softtest.rules.gcc.question;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.TreeSet;

import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTInitDeclarator;
import softtest.ast.c.ASTInitializer;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.AbstractExpression;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.VexNode;
import softtest.config.c.Config;
import softtest.domain.c.analysis.ExpressionValueVisitor;
import softtest.domain.c.analysis.ExpressionVistorData;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.IntegerDomain;
import softtest.domain.c.interval.IntegerInterval;
import softtest.domain.c.interval.PointerDomain;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.LocalScope;
import softtest.symboltable.c.SourceFileScope;
import softtest.symboltable.c.VariableNameDeclaration;

/** 
 * @author nieminhui
 * modify by yanxin
 * 函数返回局部变量的地址引用或指针
 */

public class RLVAPStateMachine {

	public 	static List<FSMMachineInstance> createRLVAPStateMachines(SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = null;
		
		//查询所有return语句后面返回的表达式
		String xpath =".//JumpStatement[@Image='return']/Expression/AssignmentExpression";
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		Iterator itr = evaluationResults.iterator();
		PointerDomain mydomain = null;
		ExpressionValueVisitor expvst = new ExpressionValueVisitor();
						ExpressionVistorData visitdata = new ExpressionVistorData();
						Domain expdomain = null;
						
						
						 
		
		while(itr.hasNext()) {
			ASTAssignmentExpression assexp = (ASTAssignmentExpression) itr.next();
			if(assexp.getImage().equals("NULL"))
			{
				continue;
			}
			
			String type = getType(assexp);
			visitdata.currentvex = assexp.getCurrentVexNode();	
			visitdata.currentvex.setfsmCompute(true);
			expvst.visit((SimpleNode)(assexp), visitdata);	
			visitdata.currentvex.setfsmCompute(false);
			expdomain=null;
			if(visitdata.value!=null){
				expdomain = visitdata.value.getDomain(visitdata.currentvex.getLastsymboldomainset());
			}
			if(expdomain !=null && expdomain instanceof IntegerDomain && !(expdomain.isUnknown())){
				IntegerDomain expIntegerDomain=(IntegerDomain)expdomain;
				TreeSet<IntegerInterval> intervalSets=expIntegerDomain.getIntervals();
				Iterator<IntegerInterval> itr11 = intervalSets.iterator();
				while(itr11.hasNext()) {
					IntegerInterval interval = itr11.next();
					if(interval.equals(new IntegerInterval(0,0)))
					{
						addFSM(list,assexp,fsm);
						continue;
					}
				}
			}
		

		
				
				
			
			if(type != null && type.contains("static"))
				continue;
			if(type != null && (type.startsWith("*") || type.startsWith("[") || type.startsWith("const *"))) {
				ASTPrimaryExpression id = (ASTPrimaryExpression)assexp.getFirstChildOfType(ASTPrimaryExpression.class);
				String idType = getType(id);
				if(idType != null && idType.contains("static"))
					continue;
				VariableNameDeclaration var = null;
				VexNode vex = null;
				if(id != null)
					var = id.getVariableNameDeclaration();
				if(var != null) {
					if(var.getScope() instanceof LocalScope) {
						if(idType != null && !idType.startsWith("*") && (type.startsWith("const *") || type.startsWith("["))) {
							addFSM(list,assexp,fsm);
							continue;	
						}
						if(idType != null && idType.startsWith("*")) {
							vex = id.getCurrentVexNode();
							if(!checkPointerIsValid(node, var, vex.getSnumber())) {
								addFSM(list,assexp,fsm);
							}
						}
					} else if(var.getScope() instanceof SourceFileScope) {
						if(idType != null && idType.startsWith("*")) {
							if(!checkPointerIsValid(node, var, Integer.MAX_VALUE)) {
								addFSM(list,assexp,fsm);
							}
						}
					}
				}
			}
		}
						
		return list;
	}
	
	private static boolean checkPointerIsValid(SimpleNode node, VariableNameDeclaration var, int num) {
		boolean isHeap = true;
		SimpleNode varExp = (SimpleNode)var.getNode();		//变量声明对应的语法树节点
		String varName = varExp.getImage();

		ASTInitDeclarator inidec = (ASTInitDeclarator)varExp.getFirstParentOfType(ASTInitDeclarator.class);
		if(inidec.jjtGetNumChildren() == 2) {
			if(inidec.jjtGetChild(1) instanceof ASTInitializer) {
				ASTInitializer ini = (ASTInitializer)inidec.jjtGetChild(1);
				isHeap = checkIsHeap(ini, node);
			}
		}
		
		int snum = -1;
		String assignXpath = ".//AssignmentExpression[./UnaryExpression//PrimaryExpression[@Image='"+varName+"']][./AssignmentOperator[@Operators='=']]";
		List<SimpleNode> assignNodeList = StateMachineUtils.getEvaluationResults(node, assignXpath);
		if(!assignNodeList.isEmpty())
		{
			for(Iterator tmpitr = assignNodeList.iterator(); tmpitr.hasNext();) {
				ASTAssignmentExpression assignNode = (ASTAssignmentExpression) tmpitr.next();
				ASTPrimaryExpression idexp =(ASTPrimaryExpression) assignNode.getFirstChildOfType(ASTPrimaryExpression.class);
				if(idexp.getVariableNameDeclaration() != null && idexp.getVariableNameDeclaration() == var) {
					if(assignNode.getCurrentVexNode().getSnumber() > snum && assignNode.getCurrentVexNode().getSnumber() < num
							&& !assignNode.getCurrentVexNode().getContradict()) {
						snum = assignNode.getCurrentVexNode().getSnumber();
						if(assignNode.jjtGetChild(2) instanceof ASTAssignmentExpression) {
							ASTAssignmentExpression assignExp = (ASTAssignmentExpression) assignNode.jjtGetChild(2);
							isHeap = checkIsHeap(assignExp, node);
						}
					}
				}
			}
		}
		else
		{
			if(inidec.jjtGetNumChildren() == 1)
			{
				isHeap = false;
			}
		}
		/*
		else
		{
			ASTInitDeclarator inidec = (ASTInitDeclarator)varExp.getFirstParentOfType(ASTInitDeclarator.class);
			if(inidec.jjtGetNumChildren() == 1)
			{
				isHeap = false;
			}
			if(inidec.jjtGetNumChildren() == 2) {
				if(inidec.jjtGetChild(1) instanceof ASTInitializer) {
					ASTInitializer ini = (ASTInitializer)inidec.jjtGetChild(1);
					isHeap = checkIsHeap(ini, node);
				}
			}
		}*/
		return isHeap;
	}
	
	private static boolean checkIsHeap(SimpleNode snode, SimpleNode root) {
//		if(snode.getImage() != null && (snode.getImage().equals("NULL") || snode.getImage().equals("0")))
//			return false;
//		if(snode.getImage() != null && snode.getImage().equals("malloc"))
//			return true;
		List idexp = snode.findChildrenOfType(ASTPrimaryExpression.class);
		int count = idexp.size();

		for(Iterator tmp = idexp.iterator(); tmp.hasNext();) {
			ASTPrimaryExpression target = (ASTPrimaryExpression) tmp.next();
			String name = target.getImage();
			String type = getType(target);
			if(type != null && type.contains("static"))
				return true;
			if(name != null && (name.equals("malloc") || name.equals("calloc") || name.equals("realloc")))
				return true;
			if(target.isMethod()) {
				return true;
			}
			if(target.getVariableNameDeclaration() != null && target.getVariableNameDeclaration().getScope() instanceof LocalScope) {
				if(type != null) {
					if(!type.startsWith("*"))
						count--;
					if(type.startsWith("*") && target.getVariableNameDeclaration() != null)
						return checkPointerIsValid(root, target.getVariableNameDeclaration(), target.getCurrentVexNode().getSnumber());
				}
			}
			if(count == 0)
				return false;
			if(target.getVariableNameDeclaration() != null && target.getVariableNameDeclaration().getScope() instanceof SourceFileScope) {
				if(type != null) {
					if(!type.startsWith("*"))
						return true;
					if(type.startsWith("*") && target.getVariableNameDeclaration() != null)
						return checkPointerIsValid(root, target.getVariableNameDeclaration(), target.getCurrentVexNode().getSnumber());
				}
			}
		}
		return true;
	}
	
	private static String getType(AbstractExpression exp) {
		if(exp != null)
			if(exp.getType() != null)
				return exp.getType().toString();
		return null;
	}

	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsmInstance = fsm.creatInstance();
		fsmInstance.setRelatedASTNode(node);
		
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) 
			fsmInstance.setDesp("return invalid pointer");
		else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
			fsmInstance.setDesp("警告：该函数返回了局部变量的地址引用或指针。" +node.getBeginLine()+
					"行这个返回的地址可能是无效的，对这个地址进行存取可能导致应用程序的不期望的行为。");
		
		list.add(fsmInstance);
	}
}
