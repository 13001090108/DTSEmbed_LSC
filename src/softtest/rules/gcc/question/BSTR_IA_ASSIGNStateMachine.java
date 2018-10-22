package softtest.rules.gcc.question;

/** 
 * @author WangJing
 * 
 */

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

public class BSTR_IA_ASSIGNStateMachine {
	
	public static List<FSMMachineInstance> createBSTR_IA_ASSIGNMachines(SimpleNode node, FSMMachine fsm) {
		
		String xpath = ".//AssignmentExpression";
		
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
		
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		Iterator itr = evaluationResults.iterator();
		
		while(itr.hasNext()) {
			
			AbstractExpression Expression = (AbstractExpression)itr.next();
			
			int childNumber = Expression.jjtGetNumChildren();
			
			if (childNumber == 3) {
				CType  type1 =  ((AbstractExpression)Expression.jjtGetChild(0)).getType();
				CType  type2 =  ((AbstractExpression)Expression.jjtGetChild(2)).getType();
				String value = ((AbstractExpression)Expression.jjtGetChild(2)).getImage();
				
				String name1 = type1.getName();
				String name2 = type2.getName();
				
				if ( "BSTR".equals(type1.getName()) && (
						(!"CcomBSTR".equals(name2)) && 
						(!"BSTR".equals(name2)) &&
						(!"bstr_t".equals(name2)) &&
						(!("".equals(value)&&("pointer".equals(name2))))																
						)){					
					addFSM(list, Expression, fsm);
				}
			}
			
		}				
		return list;
	}
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
			fsminstance.setDesp("BSTR variable may not have been initialized to NULL or a BSTR CcomBSTR , bstr_t value.");
		} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
			fsminstance.setDesp("第"+node.getBeginLine()+"行：BSTR变量可能未被初始化为NULL或BSTR、CcomBSTR、bstr_t型值。");
		}	
		list.add(fsminstance);
	}
}
