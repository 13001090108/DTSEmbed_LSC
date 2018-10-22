package softtest.rules.gcc.question;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.ASTEqualityExpression;
import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.AbstractExpression;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.Type.CType;

public class CCOMBSTR_OPS_NEStateMachine {
	
	public static List<FSMMachineInstance> createCCOMBSTR_OPS_NEStateMachines(SimpleNode node, FSMMachine fsm) {
		
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
		
		String xpath = ".//EqualityExpression[@Operators='!=']";
		
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		Iterator itr = evaluationResults.iterator();
		
		while(itr.hasNext()) {
			
			ASTEqualityExpression expression = (ASTEqualityExpression)itr.next();
			CType  type2 = null;
			if (expression == null)
				continue;
			int childNum = expression.jjtGetNumChildren();
			if (childNum != 2)
				continue;
			if(!(expression.jjtGetChild(0) instanceof ASTUnaryExpression))
			{
				continue;
			}
			CType  type1 =  ((ASTUnaryExpression)expression.jjtGetChild(0)).getType();
			if (type1 == null)
				continue;
			if (expression.jjtGetChild(1) instanceof ASTUnaryExpression)
				type2 =  ((ASTUnaryExpression)expression.jjtGetChild(1)).getType();
			else
				continue;
			if (type2 == null)
				continue;
			
			if ("CComBSTR".equals(type1.getName()) && "CComBSTR".equals(type2.getName())) {
				addFSM(list, expression, fsm);
			}
		}		
		return list;
		
	}
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
			fsminstance.setDesp("Applied to the CComBSTR entity != Compare the potential of the BSTR pointer , and no string.");
		} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
			fsminstance.setDesp("第"+node.getBeginLine()+"行：应用于CComBSTR实体的!=比较了潜在的BSTR指针，并没有进行串的比较。");
		}	
	
	}
	
}
