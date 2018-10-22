package softtest.rules.gcc.question;



import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.Type.*;

/** 
 * @author YangRui
 * 
 */

public class NSCStateMachine {

	public static List<FSMMachineInstance> createNSCStateMachines(SimpleNode node, FSMMachine fsm){
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = null;
		
		//查询所有关系表达式
		String xPath=".//RelationalExpression";
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);
		Iterator itr = evaluationResults.iterator();
		while(itr.hasNext()){
			ASTRelationalExpression relational= (ASTRelationalExpression)itr.next();
			AbstractExpression left=(AbstractExpression)relational.jjtGetChild(0);
			AbstractExpression right=(AbstractExpression)relational.jjtGetChild(1);
			if(!(left.getType() instanceof CType_BaseType)||! (right.getType() instanceof CType_BaseType) )
			continue;
			else{
				 	if(relational.getOperators().equals(">"))	{		    
					   if(left.getType().toString().equals("int")&&(left.getFirstChildOfType(ASTConstant.class))!= null&&((ASTConstant)(left.getFirstChildOfType(ASTConstant.class))).getImage().equals("0"))
						 if(right.getType().toString().equals("unsigned int"))
							addFSM(list,relational,fsm);
					   }
				 	else if(relational.getOperators().equals("<")){
					 if(right.getType().toString().equals("int")&&(right.getFirstChildOfType(ASTConstant.class))!= null&&((ASTConstant)(right.getFirstChildOfType(ASTConstant.class))).getImage().equals("0"))
						if(left.getType().toString().equals("unsigned int"))
							addFSM(list,relational,fsm);
				   }
				 	else if(relational.getOperators().equals(">=")){
						 if(right.getType().toString().equals("int")&&(right.getFirstChildOfType(ASTConstant.class))!= null&&((ASTConstant)(right.getFirstChildOfType(ASTConstant.class))).getImage().equals("0"))
							if(left.getType().toString().equals("unsigned int"))
								addFSM(list,relational,fsm);
					   }
				 	else if(relational.getOperators().equals("<=")){
				 		if(left.getType().toString().equals("int")&&(left.getFirstChildOfType(ASTConstant.class))!= null&&((ASTConstant)(left.getFirstChildOfType(ASTConstant.class))).getImage().equals("0"))
							 if(right.getType().toString().equals("unsigned int"))
								addFSM(list,relational,fsm);
					   }
				 	}
				
			}
	return list;
     
  }
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp("NoSenseCompare: It makes no sense to compare an unsigned integer with 0 like u>=0，u>0，0<=u，0<u");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("没有意义的比较: 出现比较表达式：u>=0，0<=u，0<u,u<0 时，如果变量u是一个无符号整型，则此表达式没有意义。");
			}	
		
		list.add(fsminstance);
	}
}
