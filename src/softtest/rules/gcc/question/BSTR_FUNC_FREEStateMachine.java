package softtest.rules.gcc.question;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.AbstractExpression;
import softtest.ast.c.Node;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;

/*
 * author:Wangjing
 * 模式：BSTR.FUNC.FREE：对函数SysFreeString调用不正确
 * 
 * */
public class BSTR_FUNC_FREEStateMachine {
	
	static List<SimpleNode> ls = new ArrayList<SimpleNode>();

	public static List<FSMMachineInstance> createBSTR_FUNC_FREEMachines(SimpleNode node, FSMMachine fsm) {
		
		String xpath = ".//PostfixExpression";
		
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
		
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		Iterator itr = evaluationResults.iterator();
		
		while(itr.hasNext()) {
			
			AbstractExpression PostfixExpression = (AbstractExpression)itr.next();
			
			int childNumber = PostfixExpression.jjtGetNumChildren();
			
//			System.out.println(childNumber);
			if (childNumber == 2) {
				
			    List<Node> ll  = PostfixExpression.findChildrenOfType(ASTPrimaryExpression.class);
			   
			    if (ll.size() == 2) {
			    	ASTPrimaryExpression pe1 = (ASTPrimaryExpression)ll.get(0);
			    	ASTPrimaryExpression pe2 = (ASTPrimaryExpression)ll.get(1);
			    	if(pe1==null||pe1.getType()==null||pe2==null||pe2.getType()==null)
			    	{
			    		continue;
			    	}
			    	String name1 = pe1.getType().getName();
			    	String name2 = pe2.getType().getName();
			    	
			    	if (("SysFreeString".equals(name1)) && !("BSTR".equals(name2))) {
			    		addFSM(list, PostfixExpression, fsm);
						ls.add(PostfixExpression);
			    	}
			    }				
			}			
			
		}
		
		return list;
		
	}
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		
		if(ls.contains(node))
		{
			return;
		}
		
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
			fsminstance.setDesp("The SysFreeString this function only parameter is a BSTR type.");
		} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
			fsminstance.setDesp("第"+node.getBeginLine()+"行：SysFreeString这个函数的唯一参数应该是BSTR型。");
		}	
		list.add(fsminstance);
	}
}

