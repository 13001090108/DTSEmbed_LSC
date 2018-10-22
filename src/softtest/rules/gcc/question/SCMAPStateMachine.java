package softtest.rules.gcc.question;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTExternalDeclaration;
import softtest.ast.c.ASTFieldId;
import softtest.ast.c.ASTStatement;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTPostfixExpression;
import softtest.ast.c.ASTTypeName;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.VexNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.NameOccurrence;
import softtest.symboltable.c.SourceFileScope;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.Type.CType;
import softtest.symboltable.c.Type.CType_Pointer;

/** 
 * @author nieminhui
 */

public class SCMAPStateMachine {
	public static List<FSMMachineInstance> createSCMAPStateMachines(SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = null;
	
		//查询所有malloc,recalloc,calloc函数中,sizeof函数中的变量
		String xpath = ".//PostfixExpression[./PrimaryExpression[@Image='malloc' |@Image='calloc' | @Image='realloc']]//UnaryExpression[@Image='sizeof']//TypeName";
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		Iterator itr = evaluationResults.iterator();
		while(itr.hasNext()) {
			   ASTTypeName typename = (ASTTypeName) itr.next();
			   CType type = typename.getType();
			   if(type != null && type instanceof CType_Pointer)
				   addFSM(list,typename,fsm);
		}
		
		xpath = ".//PostfixExpression[./PrimaryExpression[@Image='malloc']]/ArgumentExpressionList/AssignmentExpression//UnaryExpression[@Image!='sizeof']//AssignmentExpression//PostfixExpression " +
				"| .//PostfixExpression[./PrimaryExpression[@Image='realloc' | @Image='calloc']]/ArgumentExpressionList/AssignmentExpression[2]//UnaryExpression[@Image!='sizeof']//AssignmentExpression//PostfixExpression"; 
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);	
		itr = evaluationResults.iterator();
		while(itr.hasNext()) {
			ASTPostfixExpression post = (ASTPostfixExpression) itr.next();
			//结构体的成员变量是指针类型的
			if(post.getOperators().endsWith("->") || post.getOperators().endsWith("."))
			{
				int i = post.jjtGetNumChildren();
				ASTFieldId abstExp = (ASTFieldId) post.jjtGetChild(i-1);
				CType type = abstExp.getType();
				System.out.println(type);
				if(type != null && type instanceof CType_Pointer)
					addFSM(list,abstExp,fsm);
			}
			else
			{
				List idList = post.findChildrenOfType(ASTPrimaryExpression.class);
				if(idList.size() == 0)
					continue;
				for(Object o : idList) {
					ASTPrimaryExpression idexp = (ASTPrimaryExpression) o;
					CType type = idexp.getType();
					if(type != null && type.isPointType() && !type.toString().startsWith("["))
						addFSM(list,idexp,fsm);				
				}
			}
		}
		
		//Indirect
		xpath = ".//PostfixExpression[./PrimaryExpression[@Image='malloc']]/ArgumentExpressionList/AssignmentExpression[.//UnaryExpression[@Image!='sizeof']] " +
		"| .//PostfixExpression[./PrimaryExpression[@Image='realloc' | @Image='calloc']]/ArgumentExpressionList/AssignmentExpression[2][.//UnaryExpression[@Image!='sizeof']]";
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);	
		itr = evaluationResults.iterator();
		while(itr.hasNext()) {
			ASTAssignmentExpression ass = (ASTAssignmentExpression) itr.next();
			List idList = ass.findChildrenOfType(ASTPrimaryExpression.class);
			if(idList.size() == 0)
				continue;
			for(Object o : idList) {
				ASTPrimaryExpression idexp = (ASTPrimaryExpression) o;
				if(isDefBySizeof(idexp)) {
					addFSM(list, ass, fsm);
					break;
				}
			}
}
		return list;
	}
	
	private static boolean isDefBySizeof(ASTPrimaryExpression idexp) {
		
		VariableNameDeclaration varDecl = idexp.getVariableNameDeclaration();
		VexNode vexnode = idexp.getCurrentVexNode();
		if(varDecl != null && vexnode != null) {
			NameOccurrence occ = vexnode.getVariableNameOccurrence(varDecl);
			if(occ != null) {
				List<NameOccurrence> defs = occ.getUse_def();
				if(defs != null && defs.size() > 0) {
					NameOccurrence lastdef = defs.get(defs.size() - 1);
					List stateList = lastdef.getLocation().getParentsOfType(ASTStatement.class);
					ASTStatement state = null;
					if(stateList.size() != 0) {
						state = (ASTStatement) stateList.get(0);
					}
					if(state != null) {
						String path = ".//AssignmentExpression//UnaryExpression[@Image='sizeof']//PrimaryExpression[@DescendantDepth='0']";
						List<SimpleNode> res = StateMachineUtils.getEvaluationResults(state, path);
						for(SimpleNode snode : res) {
							ASTPrimaryExpression typename = (ASTPrimaryExpression) snode;
							if(typename.getType() instanceof CType_Pointer) {
								return true;
							}
						}
//						path = ".//assignment_expression/assignment_expression//id_expression";				//若被另一个变量赋值，则递归调用该方法
//						for(SimpleNode node : StateMachineUtils.getEvaluationResults(state, path)) {
//							if(isDefBySizeof(node))  {
//								return true;
//							}
//						}
						return false;
					}
				} else if(defs != null && defs.size() == 0 && varDecl.getScope() instanceof SourceFileScope) {
					SimpleNode varnode = varDecl.getNode();
					List declList = varnode.getParentsOfType(ASTExternalDeclaration.class);
					ASTExternalDeclaration exdecl = null;
					if(declList.size() != 0) {
						exdecl = (ASTExternalDeclaration) declList.get(0);
					}
					if(exdecl != null) {
						String path = ".//AssignmentExpression//UnaryExpression[@Image='sizeof']//TypeName";
						List<SimpleNode> res = StateMachineUtils.getEvaluationResults(exdecl, path);
						for(SimpleNode snode : res) {
							ASTTypeName typename = (ASTTypeName) snode;
							if(typename.getType() instanceof CType_Pointer) {
								return true;
							}
						}
					}
				}
			}
		}
		return false;
	}

	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsmInstance = fsm.creatInstance();
		fsmInstance.setRelatedASTNode(node);
		
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) 
			fsmInstance.setDesp("warning:sizeof may caused memory allocation problem");
		else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
			fsmInstance.setDesp("警告：sizeof可能引起内存分配问题。\r\n此处用到了sizeof返回的指针大小(32位平台上是4)。");
		
		list.add(fsmInstance);
	}
}

   