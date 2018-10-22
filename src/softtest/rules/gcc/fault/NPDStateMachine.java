package softtest.rules.gcc.fault;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import softtest.ast.c.ASTArgumentExpressionList;
import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTConditionalExpression;
import softtest.ast.c.ASTEqualityExpression;
import softtest.ast.c.ASTLogicalANDExpression;
import softtest.ast.c.ASTLogicalORExpression;
import softtest.ast.c.ASTPostfixExpression;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTStatement;
import softtest.ast.c.ASTStatementList;
import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.VexNode;
import softtest.domain.c.analysis.ConditionData;
import softtest.domain.c.analysis.ConditionDomainVisitor;
import softtest.domain.c.analysis.ExpressionValueVisitor;
import softtest.domain.c.analysis.ExpressionVistorData;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.DomainType;
import softtest.domain.c.interval.IntegerDomain;
import softtest.domain.c.interval.PointerDomain;
import softtest.domain.c.interval.PointerValue;
import softtest.domain.c.symbolic.SymbolFactor;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.Variable;
import softtest.rules.c.BasicStateMachine;
import softtest.rules.c.StateMachineUtils;
import softtest.summary.gcc.fault.MethodNPDPreConditionVisitor;
import softtest.symboltable.c.NameDeclaration;
import softtest.symboltable.c.NameOccurrence;
import softtest.symboltable.c.Scope;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.Type.CType;
import softtest.symboltable.c.Type.CType_AllocType;

public class NPDStateMachine extends BasicStateMachine {

	@Override
	public void registFetureVisitors() {
		super.registFetureVisitors();
		InterContext.addPreConditionVisitor(MethodNPDPreConditionVisitor.getInstance());
	}

	/** 对于每一个指针出现的节点，创建空指针状态机实例 */
	public static List<FSMMachineInstance> createNPDStateMachines(SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new ArrayList<FSMMachineInstance>();
		if(node.getFileName().contains(".h")==false)
		 {
		/*String xPath = ".//assignment_expression//unary_expression/postfix_expression/primary_expression/id_expression[(../../id_expression[..[@OperatorTypeString!='[.]']]) " +
				"or (../../../../unary_operator[@OperatorTypeString='[*]']) or (../../../postfix_expression[@OperatorTypeString='[[]]'])]";*/
		//xPath +="|"+".//declarator[/ptr_operator[@OperatorTypeString='[*]']]/declarator/direct_declarator/qualified_id";
		String xPath = ".//AssignmentExpression//UnaryExpression/PostfixExpression[starts-with(@Operators,'[') or starts-with(@Operators,'->')]/PrimaryExpression[@Method='false']|" +
		 ".//AssignmentExpression//UnaryExpression/PostfixExpression/PrimaryExpression[@Method='false' and ../../../UnaryOperator[@Operators='*']]";
//		String xPath = 
//			".//assignment_expression//unary_expression/postfix_expression[starts-with(@OperatorTypeString,'[[]') or starts-with(@OperatorTypeString,'[->')]/primary_expression/id_expression|" +
//			".//assignment_expression//unary_expression/postfix_expression/primary_expression/id_expression[../../../../unary_operator[@OperatorTypeString='[*]']]";
		List<SimpleNode> nodes = StateMachineUtils.getEvaluationResults(node, xPath);
		
		// 对函数内部的指针变量建立检测自动机
		HashMap<VariableNameDeclaration, LinkedList<NameOccurrence>> reoccured = new HashMap<VariableNameDeclaration, LinkedList<NameOccurrence>>(1);
		HashSet<VariableNameDeclaration> temp = new HashSet<VariableNameDeclaration>(1);
		for (SimpleNode idExp : nodes) {
			NameDeclaration decl = null;
			if (idExp instanceof ASTPrimaryExpression) {
				decl = ((ASTPrimaryExpression)idExp).getVariableNameDeclaration();
			}
			if (decl instanceof VariableNameDeclaration) {
				VariableNameDeclaration vDecl = (VariableNameDeclaration) decl;
				//if (vDecl.isParam()) {
				//	continue;
				//}
				CType type = vDecl.getType();
				//Scope scope = vDecl.getScope();
				if( (type!=null) && (type.isPointType()) 
						/*&& !(scope instanceof SourceFileScope) && !(scope instanceof ClassScope*/) {//添加全局分析之后此处可以分析成员变量NPD 
					
					List<NameOccurrence> varOccList = null;
					VexNode vex= idExp.getCurrentVexNode();
					if (vex != null) {
						for(NameOccurrence occ:vex.getOccurrences()){
							if(occ.getDeclaration()== vDecl){
								varOccList = occ.getUse_def();
								break;
							}
						}
					}
					// 同一指针的变量，定义-使用链相同则只指检测一次NPD错误
					boolean isreoccur = false;
					if (reoccured.containsKey(vDecl)) {						
						if(isSameDefUseList(varOccList, reoccured.get(vDecl))) {
							isreoccur = true;
						}
					}
					if (!isreoccur && !temp.contains(vDecl)) {
						FSMMachineInstance fsmInstance = fsm.creatInstance();
						//vDecl.setDomainGenInfo(null);
						fsmInstance.setRelatedVariable(vDecl);
						fsmInstance.setRelatedASTNode(idExp);
						if (varOccList != null) {
							reoccured.put(vDecl, (LinkedList<NameOccurrence>)varOccList);
							fsmInstance.setStateData(varOccList);
						}
						temp.add(vDecl);
						list.add(fsmInstance);
					}
				}
			}
		}
		}
		return list; 
	}
	
	private static VariableNameDeclaration findSingleParam(SimpleNode t, Variable npdVar) {
		int argIndex = -1;
		SimpleNode argNode = null;
		if (t instanceof ASTPrimaryExpression) {
			ASTPrimaryExpression node = (ASTPrimaryExpression)t;
			ASTPostfixExpression postfix = null;
			if (node.jjtGetParent() instanceof ASTPrimaryExpression) {
				postfix = (ASTPostfixExpression) node.jjtGetParent().jjtGetParent();
			} else if (node.jjtGetParent() instanceof ASTPostfixExpression) {
				postfix = (ASTPostfixExpression) node.jjtGetParent();
			}
			if (postfix == null) {
				return null;
			}
			
			// 获取形参节点，在这儿只考虑postfix里面只有一次函数调用
			List re = postfix.findDirectChildOfType(ASTArgumentExpressionList.class);
			if (re == null || re.size() <=0 ) {
				return null;
			}
			
			argNode = (ASTArgumentExpressionList)re.get(0);
		
			argIndex = npdVar.getParamIndex();
			if (argIndex < 0 && argIndex >= argNode.jjtGetNumChildren()) {
				return null;
			}
		} 
		Object result  = t.getVariableNameDeclaration();

		if (result instanceof VariableNameDeclaration) {
			return (VariableNameDeclaration)result;
		}
		return null;
	}
	
	private static boolean isSameDefUseList(List<NameOccurrence> list1, List<NameOccurrence> list2) {
		if (list1 == null && list2 == null) {
			return true;
		}
		if ((list1 == null && list2 != null) || (list1 != null && list2 == null)) {
			return false;
		}
		if (list1.size() != list2.size()) {
			return false;
		}
		//Collections.sort(list1);
		//Collections.sort(list2);
		for (int i = 0; i < list1.size(); i++) {
			if (list1.get(i).getLocation() != list2.get(i).getLocation()) {
				return false;
			}
		}
		return true;
	}
	
	private static VariableNameDeclaration findLocalVariableDecl(Variable variable, SimpleNode node) {
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

	/** 处理几种特殊情况 */
	public static boolean checkSameVariable(List nodes, FSMMachineInstance fsmin) {
		Iterator listIter = nodes.iterator();
		while (listIter.hasNext()) {
			SimpleNode idExp = (SimpleNode) listIter.next();
			/*if (idExp != fsmin.getRelatedASTNode()) {
				continue;
			}*/
			if (fsmin.getStateData() instanceof Variable) {
				return false;
			}
			if (fsmin.getStateData() != null && !(fsmin.getStateData() instanceof Variable)) {
				List<NameOccurrence> defList = (List<NameOccurrence>)fsmin.getStateData();
				if (defList.size() != 0) { 
					if (defList.get(0).getLocation().getBeginLine() > idExp.getBeginLine()) {
						continue;
					}
				}
			}
			NameDeclaration decl = null;
			if (idExp instanceof ASTPrimaryExpression) {
				decl = ((ASTPrimaryExpression)idExp).getVariableDecl();
			} 
			fsmin.setNodeUseToFindPosition(idExp);
			if (decl instanceof VariableNameDeclaration && fsmin.getRelatedVariable().getImage().equals(decl.getImage())) {
				VariableNameDeclaration vDecl = (VariableNameDeclaration) decl;
				VexNode vexNode=idExp.getCurrentVexNode();
				if(vexNode==null)
					return false;
				vexNode.setfsmCompute(true);
				Domain tempDomain=vexNode.getDomain(vDecl);
				if(tempDomain==null || tempDomain.isUnknown() || (tempDomain!=null && tempDomain.getDomaintype() == DomainType.UNKNOWN)){
					return false;
				}
				if (tempDomain instanceof PointerDomain) {
					PointerDomain pd = (PointerDomain) tempDomain; 					
					if(pd.getValue()==PointerValue.UNKOWN ) {
						return false;
					}
				}
				if (vDecl == fsmin.getRelatedVariable()) {
					VexNode vex = idExp.getCurrentVexList().get(0);
					SimpleNode treeNode = vex.getTreenode();
					if (treeNode == null) {
						return false;
					}
					if( confirmNPD(idExp, vDecl)) {
						fsmin.setRelatedASTNode(idExp);
						fsmin.setDesp("在第 " + vDecl.getNode().getBeginLine() +  " 行定义的变量\""+vDecl.getImage()+"\"可能为空指针，在第"+idExp.getBeginLine()+"行被解引用"); 
						return true;
					}
				}
			}
		}
		return false;
	}
	
	public static boolean confirmNPD(SimpleNode idExp, VariableNameDeclaration vDecl) {
		//check the condition expression eg: int j = (p == 0)? i: *p;
		ASTConditionalExpression con = (ASTConditionalExpression) idExp.getFirstParentOfType(ASTConditionalExpression.class);
		if (con != null) {
			String str = "./PostfixExpression/PrimaryExpression";
			List evaluationResults = StateMachineUtils.getEvaluationResults((SimpleNode)con.jjtGetChild(0), str);
			Iterator iterList = evaluationResults.listIterator();
			while(iterList.hasNext()){
				ASTPrimaryExpression temp = (ASTPrimaryExpression) iterList.next();
				if(temp.getVariableDecl()!= vDecl){
					continue;
				}
				ASTEqualityExpression equal = (ASTEqualityExpression)temp.getFirstParentOfType(ASTEqualityExpression.class);
				if(equal == null || equal.jjtGetNumChildren()>1){
					return false;
				}					
			}
		}
		// 检查表达式短路: if (p!=null && *p==1) 或者 if (p && *p==1)
		ASTLogicalANDExpression expressionAnd = (ASTLogicalANDExpression)idExp.getFirstParentOfType(ASTLogicalANDExpression.class);
		if (expressionAnd != null && expressionAnd.jjtGetNumChildren() >= 2) {
			for (int i = 0; i < expressionAnd.jjtGetNumChildren(); i++) {
				SimpleNode expNode = (SimpleNode)expressionAnd.jjtGetChild(i);
				if (idExp.isSelOrAncestor(expNode)) {
					break;
				}
				
				// p 的may集合是不是为非空
				ConditionDomainVisitor condVisitor = new ConditionDomainVisitor();
				ConditionData condData = new ConditionData(idExp.getCurrentVexNode());
				expNode.jjtAccept(condVisitor, condData);
				if (idExp.getCurrentVexNode().getValue(vDecl) == null || idExp.getCurrentVexNode().getValue(vDecl).getSingleFactor() == null) {
					continue;
				}
				if (!(idExp.getCurrentVexNode().getValue(vDecl).getSingleFactor() instanceof SymbolFactor)) {
					continue;
				}
				Domain pDomain = condData.getMayDomain((SymbolFactor) idExp.getCurrentVexNode().getValue(vDecl).getSingleFactor());
				if (pDomain != null && !pDomain.isUnknown() && pDomain instanceof PointerDomain && pDomain.getDomaintype() != DomainType.UNKNOWN) {
					PointerDomain point = (PointerDomain)pDomain;
					if (point.getValue() == PointerValue.EMPTY || !point.offsetRange.contains(0)) {
						return false;
					}
				}
				// 判断是否有恒假分支
				ExpressionValueVisitor exp = new ExpressionValueVisitor();
				ExpressionVistorData domaindata = new ExpressionVistorData();
				domaindata.currentvex = idExp.getCurrentVexNode();
				exp.visit((SimpleNode)idExp, domaindata);
//				if (domaindata.currentvex.getDomain((VariableNameDeclaration)idExp.getVariableNameDeclaration()) instanceof BooleanDomain && !domaindata.domain.isUnknown()) {
//					BooleanDomain bDomain = (BooleanDomain)domaindata.domain;
//					if (bDomain.getValue() == BooleanValue.FALSE) {
//						return false;
//					}
//				} else
				VariableNameDeclaration re = (VariableNameDeclaration)idExp.getVariableNameDeclaration();
				if (re == null) {
					continue;
				}
				Domain domain =domaindata.currentvex.getDomain(re);
				if (domain instanceof IntegerDomain && !domain.isUnknown() && domain.getDomaintype() != DomainType.UNKNOWN) {
					IntegerDomain iDomain = (IntegerDomain)domain;
					if (iDomain.isCanonical() && iDomain.jointoOneInterval().getMin() == 0) {
						return false;
					}
				}
			}
		}
		// 检查表达式短路: if(!p || *p==1) 或者 if (p == (void*)0 || *p==1)  
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
				if (idExp.getCurrentVexNode().getValue(vDecl) == null || idExp.getCurrentVexNode().getValue(vDecl).getSingleFactor() == null) {
					continue;
				}
				if (!(idExp.getCurrentVexNode().getValue(vDecl).getSingleFactor() instanceof SymbolFactor)) {
					continue;
				}
				Domain pDomain = condData.getMayDomain((SymbolFactor) idExp.getCurrentVexNode().getValue(vDecl).getSingleFactor());
				if (pDomain != null && !pDomain.isUnknown() && pDomain instanceof PointerDomain && pDomain.getDomaintype() != DomainType.UNKNOWN) {
					PointerDomain point = (PointerDomain)pDomain;
					if (point.isCanonical() && point.getValue() == PointerValue.NULL ) {
						return false;
					}
				}
				// 判断是否有恒真分支
				ExpressionValueVisitor exp = new ExpressionValueVisitor();
				ExpressionVistorData domaindata = new ExpressionVistorData();
				domaindata.currentvex = idExp.getCurrentVexNode();
				exp.visit((SimpleNode)idExp, domaindata);//zys:idExp有可能为叶子节点，无孩子，所以空指针异常了
//				if (domaindata.domain instanceof BooleanDomain && !domaindata.domain.isUnknown()) {
//					BooleanDomain bDomain = (BooleanDomain)domaindata.domain;
//					if (bDomain.getValue() == BooleanValue.TRUE) {
//						return false;
//					}
//				} else
				VariableNameDeclaration re = (VariableNameDeclaration)idExp.getVariableNameDeclaration();
				if (re == null) {
					continue;
				}
				Domain domain =domaindata.currentvex.getDomain(re);
				if (domain instanceof IntegerDomain && !domain.isUnknown() && domain.getDomaintype() != DomainType.UNKNOWN) {
					IntegerDomain iDomain = (IntegerDomain)domain;
					if (iDomain.isCanonical() && iDomain.jointoOneInterval().getMin() == 0) {
						return false;
					}
				}
			}
		}
		
		// 确保不是sizeof(*p)
		boolean isSizeof = false;
		SimpleNode node = (SimpleNode)idExp.jjtGetParent();
		while (!(node instanceof ASTStatement) && node.jjtGetNumChildren() <= 2) {
			if (node instanceof ASTUnaryExpression && node.getImage().equals("sizeof")) {
				isSizeof = true;
				break;
			} else if (node instanceof ASTAssignmentExpression && node.jjtGetNumChildren() >= 2) {
				break;
			}
			node = (SimpleNode)node.jjtGetParent();
		}
		if (isSizeof) {
			return false;
		}
		return true;
	}
	public static boolean checkFollowed(VexNode node,FSMMachineInstance fsmin){
		if(fsmin.getRelatedVariable()==null)
			return false;
		String var=((VariableNameDeclaration)fsmin.getRelatedVariable()).getImage();	
		SimpleNode simnode=node.getTreenode();
		Domain pDomain=node.getDomain((VariableNameDeclaration)fsmin.getRelatedVariable());
		boolean isUnknowPoint=false;
		if(pDomain instanceof PointerDomain &&!pDomain.isUnknown() && pDomain.getDomaintype() == DomainType.UNKNOWN){
			isUnknowPoint=true;
		}
		ASTStatementList stat_list=(ASTStatementList)simnode.getFirstParentOfType(ASTStatementList.class);
		if(stat_list!=null && isUnknowPoint){
			String xpath=".//SelectionStatement/Expression/SssignmentExpression//UnaryExpression[./UnaryOperator[@Image='!']]/UnaryExpression/PostfixExpression[count(*)<=1]/PrimaryExpression[@Image='"+var+"']"
			+"|.//SelectionStatement/Expression/AssignmentExpression//UnaryExpression/PostfixExpression[count(*)<=1]/PrimaryExpression[@Image='"+var+"']";
			List evaluationResults = StateMachineUtils.getEvaluationResults(stat_list, xpath);	
			Iterator iter=evaluationResults.iterator();
			while(iter.hasNext()){
				ASTPrimaryExpression idexp=(ASTPrimaryExpression)iter.next();
				if(node!=idexp.getCurrentVexNode()){
					//pDomain.setUnknown(false);
					//node.addDomain((VariableNameDeclaration)fsmin.getRelatedVariable(), pDomain);
					return true;
				}
			}
		}
		return false;
	}
}
