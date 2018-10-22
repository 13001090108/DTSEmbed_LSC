package softtest.rules.gcc.rule;

import java.util.LinkedList;
import java.util.List;


import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.*;
import softtest.symboltable.c.Type.*;


/** 
 * @author nieminhui
 * Assign Negative To Unsigned variable
 * 禁止给无符号变量赋负值
 */
public class ANTUStateMachine {
	
	//找到所有赋值操作
	private static final String xpath = ".//AssignmentExpression";
	//赋值表达式的左值
	private static final String xpath1 = "./UnaryExpression/PostfixExpression/PrimaryExpression[@DescendantDepth='0']";
	//赋值表达式右值为负的Constant型
	private static final String xpath2 = "./AssignmentExpression/UnaryExpression[./UnaryOperator[@Operators='-']]/UnaryExpression/PostfixExpression/PrimaryExpression/Constant";
	//赋值表达式右值为负的unsigned型
	private static final String xpath3 = "./AssignmentExpression/UnaryExpression[./UnaryOperator[@Operators='-']]/UnaryExpression/PostfixExpression/PrimaryExpression[@DescendantDepth='0']";

	public static List<FSMMachineInstance> createANTUMachines(SimpleNode node, FSMMachine fsm){
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
		
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		SimpleNode var = null; //赋值表达式的左值
		
		for (SimpleNode snode : evaluationResults) {
			List<SimpleNode> vars = StateMachineUtils.getEvaluationResults(snode, xpath1);
			if(vars!=null && vars.size()==1)
				var = vars.get(0);
			else 
				continue;
			
			VariableNameDeclaration variable = var.getVariableNameDeclaration();
			if(!(variable!=null && isUnsignedType(variable.getType()))) //左值是Unsigned类型
				continue;
			
			List<SimpleNode> constants = StateMachineUtils.getEvaluationResults(snode, xpath2);//右值是负的Constant类型
			if(constants!=null && constants.size()==1) {	
				addFSMDescription(snode, variable, fsm, list);
				continue;
			}	
			
			List<SimpleNode> values = StateMachineUtils.getEvaluationResults(snode, xpath3);//右值是负的Unsigned类型
			if(values!=null && values.size()==1) {
				SimpleNode rightVar = values.get(0);
				VariableNameDeclaration rightVarDel = rightVar.getVariableNameDeclaration();
				if(rightVarDel!=null && isUnsignedType(rightVarDel.getType())) 
					addFSMDescription(snode, variable, fsm, list);
			}
		}
	    return list;
	}	
	
	private static boolean isUnsignedType(CType type) {
		if(!(type instanceof CType_BaseType))
			return false;
		if(type == CType_BaseType.uCharType || type == CType_BaseType.uIntType || type == CType_BaseType.uLongLongType || type == CType_BaseType.uLongType || type == CType_BaseType.uShortType )
			return true;
		return false;
	}

	private static void addFSMDescription( SimpleNode node, VariableNameDeclaration variable, FSMMachine fsm, List<FSMMachineInstance> list) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp(" Assign Negative To Unsigned Variable " + variable.getImage() + ". This will lead to unpredictable result.");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("禁止给无符号变量" + variable.getImage() + "赋负值。\r\n给无符号变量赋负值会导致不可预料的结果。");
			}	
		
		list.add(fsminstance);
	}
}
