package softtest.rules.gcc.question;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.ASTArgumentExpressionList;
import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.AbstractExpression;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.Type.CType;

/*
 * author:Wangjing
 * 模式：BSTR.FUNC.REALLOC：BSTR重分配函数错误使用(Question:BSTR)
 * 
 * */
public class BSTR_FUNC_REALLOCStateMachine {
	
	public static List<FSMMachineInstance> createBSTR_FUNC_REALLOCMachines(SimpleNode node, FSMMachine fsm) {
		
		String xpath = ".//PostfixExpression";
		
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
		
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		Iterator itr = evaluationResults.iterator();
		
		while(itr.hasNext()) {
			
			AbstractExpression Expression = (AbstractExpression)itr.next();
			
			if (Expression == null)
				continue;
			int childNumber = Expression.jjtGetNumChildren();
			
			if (childNumber == 2) {
				
				ASTPrimaryExpression  astpe =  (ASTPrimaryExpression)Expression.jjtGetChild(0);
				ASTArgumentExpressionList astae;
				
				if (Expression.jjtGetChild(1) instanceof ASTArgumentExpressionList)
				    astae =  (ASTArgumentExpressionList)Expression.jjtGetChild(1);
				else
					continue;
				
				if (astae == null)
					continue;

				String funName = astpe.getImage();
				int childs = astae.jjtGetNumChildren();
				
				if (("SysReAllocString".equals(funName) || "SysReAllocStringLen".equals(funName)) && (childs == 2)) {
					ASTAssignmentExpression astae1 = (ASTAssignmentExpression)astae.jjtGetChild(0);
					ASTAssignmentExpression astae2 = (ASTAssignmentExpression)astae.jjtGetChild(1);
					if(astae1==null||astae2==null)
			    	{
			    		continue;
			    	}
					CType type1 = astae1.getType();
					CType type2 = astae2.getType();
					if(type1==null||type2==null)
			    	{
			    		continue;
			    	}
					String type11 = type1.toString();
					String type22 = type2.toString();
					
					if ((!type11.contains("*BSTR")) || (!type22.contains("*wchar_t")))
						addFSM(list, Expression, fsm);
				}				
			}			
		}				
		return list;
	}
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
			fsminstance.setDesp("The first parameter of the the SysReAllocString SysReAllocStringLen function should be a pointer to pointer to a BSTR instance . The second argument should be a wide character string.");
		} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
			fsminstance.setDesp("第"+node.getBeginLine()+"行：SysReAllocString和SysReAllocStringLen函数的第一个参数应该是指向BSTR实例的指针,第二个参数应该是宽字符型字符串。");
		}	
		list.add(fsminstance);
	}
}
