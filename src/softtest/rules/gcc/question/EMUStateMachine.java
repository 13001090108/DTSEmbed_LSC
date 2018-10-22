package softtest.rules.gcc.question;

import java.util.*;

import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.*;


/** 
 * @author nieminhui
 * 枚举类型的混用错误
 */

public class EMUStateMachine {
	/**
	 * @param node
	 * @param fsm
	 * @return
	 */
	public static List<FSMMachineInstance> createEMUStateMachines(SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = null;
		//查询所有if语句中的判断表达式
		String xpath = ".//SelectionStatement[@Image='if']/Expression/AssignmentExpression/EqualityExpression";
		
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		Iterator itr = evaluationResults.iterator();
		while(itr.hasNext()) {
			SimpleNode snode =(SimpleNode) itr.next();
			
			AbstractExpression exp1 = (AbstractExpression)snode.jjtGetChild(0);
			AbstractExpression exp2 = (AbstractExpression)snode.jjtGetChild(1);
            
			String type1 = getType(exp1);
			String type2 = getType(exp2);			
			//System.out.println(type1);
			//System.out.println(type2);
			if(type1 != null && type2 != null) {
				if(type1.startsWith("enum") && type2.equals("int"))
					if(isMixedUse(type1,exp2))
						addFSM(list,snode,fsm,"if");
				if(type2.startsWith("enum") && type1.equals("int"))
					if(isMixedUse(type2,exp1))
						addFSM(list,snode,fsm,"if");
			}
				
		}
		
		//查询所有switch语句后面的表达式
		xpath = ".//SelectionStatement[@Image='switch']/Expression";
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		itr = evaluationResults.iterator();
		while(itr.hasNext()) {
			ASTExpression exp = (ASTExpression) itr.next();
			String type = getType(exp);
			if(type != null && type.contains("enum")) {
				//查询每个switch语句块中case后面的表达式
				String xpathLabel = xpath + "[@Image='" + exp.getImage() + "'][@BeginLine='"
				+ exp.getBeginLine() + "']/parent::*//LabeledStatement[@Image='case']/ConstantExpression";
				List<SimpleNode> resultLabel = StateMachineUtils.getEvaluationResults(node, xpathLabel);
				Iterator itrLabel = resultLabel.iterator();
				while(itrLabel.hasNext()) {
					ASTConstantExpression con = (ASTConstantExpression) itrLabel.next();
					String contype = getType(con);
					if(contype != null && contype.equals("int"))
						if(isMixedUse(type,con))
							addFSM(list,con,fsm,"switch");
				}
			}
		}

		return list;
	}

	private static String getType(AbstractExpression exp) {
		if(exp.getType() != null)
			return exp.getType().toString();
		else
			return null;
	}
	
	private static boolean isMixedUse(String enumType,AbstractExpression constintType) {
		VariableNameDeclaration varDecl =constintType.getVariableNameDeclaration();
		String enumName = null;
		ASTEnumerator enumerator = null;
		if(varDecl != null)
			if(varDecl.getNode() instanceof ASTEnumerator)
				enumerator = (ASTEnumerator)varDecl.getNode();
			else 
				return false;
		if(enumerator != null)
			enumName =((ASTEnumSpecifier) enumerator.jjtGetParent().jjtGetParent()).getImage();
		if(enumName == null)
			return false;
		enumName = "enum " + enumName;
		if(enumType.equals(enumName))
			return false;
		else
			return true;	
	}
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm, String var) {
		FSMMachineInstance fsmInstance = fsm.creatInstance();
		fsmInstance.setRelatedASTNode(node);		
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) 		
			fsmInstance.setDesp("mixed use enum type in sentence "+ var);
		else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
			fsmInstance.setDesp("运算中出现了枚举类型的混用。因为来自不同枚举类型的枚举成员可能有相同的值但是不同的意思。\n在 " + var + " 语句中第"+node.getBeginLine()+"行使用不同的枚举类型可能产生问题。" );
		list.add(fsmInstance);
	}
	
}












