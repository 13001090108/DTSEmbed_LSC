package softtest.rules.gcc.question;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTCompoundStatement;
import softtest.ast.c.ASTInitDeclarator;
import softtest.ast.c.ASTInitializer;
import softtest.ast.c.ASTIterationStatement;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTSelectionStatement;
import softtest.ast.c.ASTStatement;
import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.AbstractExpression;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.LocalScope;
import softtest.symboltable.c.NameOccurrence;
import softtest.symboltable.c.Scope;
import softtest.symboltable.c.SourceFileScope;
import softtest.symboltable.c.VariableNameDeclaration;

/*
 * @author yanxin
 *本地变量地址全局返回
 */
public class GLOBStateMachine {

	public static List<FSMMachineInstance> createGLOBStateMachines(SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = null;
		ASTTranslationUnit  translationUnitNode = (ASTTranslationUnit)node.getFirstParentOfType(ASTTranslationUnit.class);
		if(translationUnitNode==null)
		{
			return list;
		}
		
		String xpath =".//Declaration//Declarator/DirectDeclarator";
		evaluationResults = StateMachineUtils.getEvaluationResults( translationUnitNode, xpath);
		Iterator itr = evaluationResults.iterator();
		
		while(itr.hasNext()) {
			SimpleNode sNode = (SimpleNode)itr.next();
			if(sNode.getVariableNameDeclaration()==null||sNode.getVariableNameDeclaration().getScope() instanceof LocalScope)
			{
				continue;
			}
			
			VariableNameDeclaration var = sNode.getVariableNameDeclaration();
			if(var==null||var.getType()==null||!var.getType().isPointType())
				continue;
			Scope scope = sNode.getVariableNameDeclaration().getScope();
			Map<VariableNameDeclaration, ArrayList<NameOccurrence>> varOccs = scope.getVariableDeclarations();
			List<NameOccurrence> occs = varOccs.get(var);
			Iterator itroccs = occs.iterator();
			
			
			ASTSelectionStatement flagSelect = null;
			ASTIterationStatement flagIter = null;
			ASTCompoundStatement flagState = null;
			int occsNumber=occs.size() -1;
			for(;occsNumber>=0;occsNumber--){
				NameOccurrence occ =occs.get(occsNumber);
				if(occ.getOccurrenceType() == NameOccurrence.OccurrenceType.DEF)
				{    
					 SimpleNode va = (SimpleNode)occ.getLocation();
					 ASTAssignmentExpression assign=( ASTAssignmentExpression ) va.getFirstParentOfType(ASTAssignmentExpression.class);
					 if(assign!=null&&assign.jjtGetChild(2)!=null)
					 { SimpleNode simple = (SimpleNode)assign.jjtGetChild(2);
					 ASTPrimaryExpression pri = (ASTPrimaryExpression)simple.getFirstChildOfType(ASTPrimaryExpression.class);
					 if(flagState!=null&&flagState == (ASTCompoundStatement)va.getFirstParentOfType(ASTCompoundStatement.class))
				    	   continue;
					 if(flagIter!=null&&flagIter==(ASTIterationStatement)va.getFirstParentOfType(ASTIterationStatement.class))
						    continue;
//					 if(flagSelect!=null&&flagSelect!=(ASTSelectionStatement)va.getFirstParentOfType(ASTSelectionStatement.class)&&)
//					     break;
					 if(flagSelect!=null&&va.getFirstParentOfType(ASTSelectionStatement.class) == null)
						 break;
					 
					 if( !checkIsHeap(pri,node))
							addFSM(list, pri, fsm);
					 if(va.getFirstParentOfType(ASTSelectionStatement.class)!=null)
					 {  
//					       if(flagState == (ASTCompoundStatement)va.getFirstParentOfType(ASTCompoundStatement.class))
//					    	   continue;
						 
//						 if(flagSelect!=null&&flagSelect==(ASTSelectionStatement)va.getFirstParentOfType(ASTSelectionStatement.class))
//						     break;
						 flagSelect = (ASTSelectionStatement) va.getFirstParentOfType(ASTSelectionStatement.class);
					     flagState = (ASTCompoundStatement)va.getFirstParentOfType(ASTCompoundStatement.class);
						         continue;
					 }
					 if(va.getFirstParentOfType(ASTIterationStatement.class)!=null)
					 {    // if(flagState == (ASTCompoundStatement)va.getFirstParentOfType(ASTCompoundStatement.class))
//				    	   continue;
					 
						  flagIter = (ASTIterationStatement) va.getFirstParentOfType(ASTIterationStatement.class);
//						  flagState = (ASTCompoundStatement)va.getFirstParentOfType(ASTCompoundStatement.class); 
						  continue;
						 
					 }	 
						
					
					 
					 break;
				}
				}
				  
			}
			
			
			
				
			
		}
		 return list;
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
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsmInstance = fsm.creatInstance();
		fsmInstance.setRelatedASTNode(node);
		
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) 		
			fsmInstance.setDesp("Warning: Line" + fsmInstance.getRelatedASTNode().getBeginLine()+" Locate varible globle used");
		else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
			fsmInstance.setDesp("警告：第" + fsmInstance.getRelatedASTNode().getBeginLine()+" 行局部变量全局使用");
		
		list.add(fsmInstance);
	}
}
