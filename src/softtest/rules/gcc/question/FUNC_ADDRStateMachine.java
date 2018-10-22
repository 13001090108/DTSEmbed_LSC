package softtest.rules.gcc.question;

import java.util.Iterator;

import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.ASTConstant;
import softtest.ast.c.ASTEqualityExpression;
import softtest.ast.c.AbstractExpression;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.Type.CType;
import softtest.symboltable.c.Type.CType_BaseType;
import softtest.symboltable.c.Type.CType_Function;

/** 
 *  
 * @author by WangJing
 * 函数地址不为0，因此函数地址与0比较为false或者true
 */
public class FUNC_ADDRStateMachine {
	
	public static List<FSMMachineInstance> createFUNC_ADDRStateMachines(SimpleNode node, FSMMachine fsm) {
		
		String xpath = ".//EqualityExpression";
		
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
		
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		Iterator itr = evaluationResults.iterator();
		while(itr.hasNext()) {
			AbstractExpression EqualityExpression = (AbstractExpression)itr.next();
			if (EqualityExpression == null)
				continue;
			
			int childNum = EqualityExpression.jjtGetNumChildren();
			if (childNum != 2)
				continue;
			
			CType type1 =  ((AbstractExpression)EqualityExpression.jjtGetChild(0)).getType();
			String child1 = ((AbstractExpression)EqualityExpression.jjtGetChild(0)).getImage();
			CType type2 = null;
			if (EqualityExpression.jjtGetChild(1) instanceof AbstractExpression)
				type2 = ((AbstractExpression)EqualityExpression.jjtGetChild(1)).getType();
			else
				continue;
			String child2 = ((AbstractExpression)EqualityExpression.jjtGetChild(1)).getImage();			
			
			ASTConstant astConstant =(ASTConstant) EqualityExpression.getFirstChildOfType(ASTConstant.class);
			if (astConstant == null)
				continue;
			CType astConstantType = astConstant.getType();
			if (astConstantType == null)
				continue;
			String astValue = astConstant.getImage();
			
			if (type1 instanceof CType_Function && type2 instanceof CType_BaseType && astValue.equals("0"))
				addFSM(list, EqualityExpression, fsm);
			else if (type2 instanceof CType_Function && type1 instanceof CType_BaseType && astValue.equals("0"))
				addFSM(list, EqualityExpression, fsm);
		}
		
		return list;
	}
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
			fsminstance.setDesp("Address of the function compares with 0.");
		} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
			fsminstance.setDesp("第"+node.getBeginLine()+"行：函数地址与0进行比较。");
		}
		
		list.add(fsminstance);
	}
}
