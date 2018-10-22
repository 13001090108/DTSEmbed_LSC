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
 * @author 
 * Avoid Comma Operator(推荐类)
 * 避免使用逗号操作符(除非在参数表或循环中可以使用逗号操作符)
 */
public class ACOStateMachine {	
	
	
	public static List<FSMMachineInstance> createACOMachines(SimpleNode node, FSMMachine fsm){
		//找到逗号操作符的表达式
		String xpath = ".//Expression[count(child::AssignmentExpression)>1]";
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
		
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);	
		for (SimpleNode snode : evaluationResults) {
			//循环中可以使用逗号操作符
			if(snode.jjtGetParent() instanceof ASTIterationStatement)
				continue;
			//除去new AVIReadCache(fcc== 'sdiv' ? 131072 : 16384, streamno);情况
			if(snode.jjtGetParent() instanceof ASTConditionalExpression)
				continue;
			//除去assert(f)特殊情况，预处理后变为(void)( (f) || (_assert("f", "F:\\1.cpp", 6), 0) );
			if(snode.getImage()!= null && snode.getImage().equals("_assert"))
			//if(snode.getImageS()!= null && snode.getImages().size() >= 1 && snode.getImages().get(0).equals("_assert"))
				continue;
			
			addFSMDescription(snode,fsm, list);
		}
	    return list;
	}	

	private static void addFSMDescription(SimpleNode node, FSMMachine fsm, List<FSMMachineInstance> list) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp("avoid using comma operator. Using comma operator will reduce the readability of the code.");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("避免使用逗号操作符。\r\n除非在参数表或循环中可以使用逗号操作符，否则逗号操作符的使用会使程序的可读性降低。");
			}	
		
		list.add(fsminstance);
	}
}

