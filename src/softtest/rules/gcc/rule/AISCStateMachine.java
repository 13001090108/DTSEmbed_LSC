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
 * Assignment operation In Short Circult operation
 * 禁止赋值操作符与“&&”或“‖”连用
 * (由于短路运算符的特性，赋值操作符如果出现在非第一个表达式中，由于赋值被条件化，有可能赋值语句没法执行)
 */
public class AISCStateMachine {	
	
	
	public static List<FSMMachineInstance> createAISCMachines(SimpleNode node, FSMMachine fsm){
		//找到所有的&&与||表达式 
		String xpath = ".//LogicalANDExpression | .//LogicalORExpression";
		//找到表达式中含有赋值运算符"="的表达式
		String xpath1 = ".//AssignmentExpression[/AssignmentOperator[@Operators='=']]";
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
		
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);	
		for (SimpleNode snode : evaluationResults) {
			int nCount = snode.jjtGetNumChildren();
			//处理a && b && c的情况（b,c都需考虑）
			for(int i=1; i<nCount; i++) {
				SimpleNode child = (SimpleNode) snode.jjtGetChild(i);
				List<SimpleNode> assign = StateMachineUtils.getEvaluationResults(child, xpath1);
				if(assign==null || assign.size()==0)
					continue;
				addFSMDescription(snode, child, fsm, list);
			}
		}
	    return list;
	}	

	private static void addFSMDescription(SimpleNode parent, SimpleNode node, FSMMachine fsm, List<FSMMachineInstance> list) {
		String engDes = "||";
		if(parent instanceof ASTLogicalANDExpression) 
			engDes = "&&";
		
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp("Assignment operation In Short Circult operation " +  engDes + ". This is a bad programming habit.");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("禁止赋值操作符与 "+ engDes + " 连用。\r\n这是一种不好的编程习惯，因为赋值被条件化了，原期望的赋值未必能被执行。");
			}	
		
		list.add(fsminstance);
	}
}
