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
 * 模式：BSTR.FUNC.LEN：特定函数获得BSTR串的长度(Question:BSTR)
 * 
 * */
public class BSTR_FUNC_LENStateMachine {
	
	static List<SimpleNode> ls = new ArrayList<SimpleNode>();

	public static List<FSMMachineInstance> createBSTR_FUNC_LENMachines(SimpleNode node, FSMMachine fsm) {
		
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
			    	
			    	if ((("SysStringLen".equals(name1)) || ("SysStringByteLen".equals(name1))) && 
			    			!("BSTR".equals(name2) ||
			    			  "CComBSTR".equals(name2) ||
			    			  "CComBSTR".equals(name2))) {
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
		
		if(ls.contains(node)) {
			return;
		}
		
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
			fsminstance.setDesp("SysStringLen or SysStringByteLen function's only parameter type should be as follows: BSTR , CComBSTR or bstr_t.");
		} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
			fsminstance.setDesp("第"+node.getBeginLine()+"行：SysStringLen或SysStringByteLen函数唯一的参数的类型应该为：BSTR, CComBSTR或bstr_t。");
		}	
		list.add(fsminstance);
	}
}
