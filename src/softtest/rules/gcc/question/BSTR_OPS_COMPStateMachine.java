package softtest.rules.gcc.question;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.AbstractExpression;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.Type.CType;

/*
 * 
 * 作者：王靖
 * 模式：BSTR变量比较(Question:BSTR)
 * 参数：需要在run arguments中的vm中加上-Xmx128m否则会出现java heap space错误
 * */
public class BSTR_OPS_COMPStateMachine {
	public static List<FSMMachineInstance> createBSTR_OPS_COMPMachines(SimpleNode node, FSMMachine fsm) {
		

		String xpath = ".//RelationalExpression";
		
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();	
		List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();	
		
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		Iterator itr = evaluationResults.iterator();
		
		while(itr.hasNext()){
			
			AbstractExpression RelationalExpression = (AbstractExpression)itr.next();	
			
			CType  type1 =  ((AbstractExpression)RelationalExpression.jjtGetChild(0)).getType();
			CType  type2 =  ((AbstractExpression)RelationalExpression.jjtGetChild(1)).getType();
			
			if(type1 == null || type2 == null  )
				continue;
			
			if("BSTR".equals(type1.getName())|| "BSTR".equals(type2.getName()))
				addFSM(list, RelationalExpression, fsm);
		}
	    return list;
	}	
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
			fsminstance.setDesp("BSTR value of type can not be with any other type of value less than, greater than, less than or equal to , greater than or equal to operator.");
		} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
			fsminstance.setDesp("第"+node.getBeginLine()+"行：BSTR类型的值不能与其他任何类型的数值进行小于、大于、小于等于、大于等于运算。");
		}	
		
		list.add(fsminstance);
	}

}
