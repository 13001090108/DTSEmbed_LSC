package softtest.rules.gcc.question;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.ASTParameterDeclaration;
import softtest.ast.c.ASTParameterList;
import softtest.ast.c.AbstractExpression;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.Type.CType;


/** 
 * @author WangJing
 * 传值引用的函数参数太大
 */

public class PARAMStateMachine {

	public static List<FSMMachineInstance> createPARAMStateMachines(SimpleNode node, FSMMachine fsm) {
		
		String xpath = ".//FunctionDefinition//ParameterList";
		
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
		
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		Iterator itr = evaluationResults.iterator();
		
		while(itr.hasNext()) {
			
			ASTParameterList parameters = (ASTParameterList)itr.next();
			
			int childNumber = parameters.jjtGetNumChildren();
			
			int totalSize = 0;
			
			for (int i = 0; i < childNumber; ++i) {
				
				ASTParameterDeclaration parameter = (ASTParameterDeclaration)parameters.jjtGetChild(i);
				
				CType type = parameter.getType();
				
				int currentSize = type.getSize();
				
				totalSize += currentSize;
				
				if (currentSize > 200 || totalSize > 200) {
					
					addFSM(list, parameter, fsm);
					
				}								
			}			
		}				
		return list;
	}
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
			fsminstance.setDesp("Pass by value reference function parameters is too large.");
		} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
			fsminstance.setDesp("第"+node.getBeginLine()+"行：传值引用的函数参数太大。");
		}	
		list.add(fsminstance);
	}
}
