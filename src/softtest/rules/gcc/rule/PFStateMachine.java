package softtest.rules.gcc.rule;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;

/** 
 * @author DongNa
 * 禁止将过程声明为指针类型
 * ProcedurePointer
 */

public class PFStateMachine {

	public static List<FSMMachineInstance> createPFStateMachines(SimpleNode node, FSMMachine fsm){
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = null;
		
		/*查询函数指针类型的声明（参数为空和不为空的）
	  	形式1：返回类型(*函数名)(参数表) 
		形式2：typedef 返回类型(*新类型)(参数表) ??
		
	*/		
		String xPath=".//Declaration/InitDeclaratorList/InitDeclarator/Declarator/DirectDeclarator/Declarator[/Pointer]";
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);
		Iterator itr = evaluationResults.iterator();
		                                                                                                                                                                                                                                                                                                                                                                                                                                                
		while(itr.hasNext()){
			ASTDeclarator id = (ASTDeclarator)itr.next();
			addFSM(list,id,fsm);
			}
		return list;
		
  }
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp("ProcedurePointer: Using function pointer is dangerous,so it's banded to use function pointer.");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("在第"+node.getBeginFileLine()+"行出现过程声明为指针类型: 使用过程指针是具有较大风险的，因此禁止将过程声明为指针类型。");
			}	
		
		list.add(fsminstance);
	}
}



