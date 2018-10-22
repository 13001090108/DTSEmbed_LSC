package softtest.rules.gcc.rule;

import java.util.ArrayList;
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
 * @author maojinyu
 * 使用不合适的循环变量类型
 * ImproperLoopVariable
 */

public class ILVStateMachine {

	public static List<FSMMachineInstance> createILVStateMachines(SimpleNode node, FSMMachine fsm){
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = null;
		
		String xPath=".//IterationStatement[@Image='for']";
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);
		Iterator itr = evaluationResults.iterator();
		
		while(itr.hasNext()){
			ASTIterationStatement iter= (ASTIterationStatement)itr.next();
			int i=iter.jjtGetNumChildren();
			switch (i)
			{
			case 1: //for的三个表达式都省略
				break;
			case 2://for省略两个表达式
				break;
									 
			case 3://for省略一个表达式
				String relationCase3xPath = "//RelationalExpression|//EqualityExpression";
				List<SimpleNode> case3Result = null;
				case3Result = StateMachineUtils.getEvaluationResults(iter, relationCase3xPath);
				
				if (case3Result == null)
					//省略的是第二项判断表达式
					break;
				
				Iterator case3itr = case3Result.iterator();
				 while(case3itr.hasNext()){
						SimpleNode exp= (SimpleNode)case3itr.next();
						List<Node> case3conList = exp.findChildrenOfType(ASTPrimaryExpression.class);
						if (case3conList == null)
							continue;
						
						//省略的是第三项初始化表达式
						if(!exp.isSelOrAncestor((SimpleNode)iter.jjtGetChild(0)))
							break;
						
						//省略的是第一项初始化表达式
						List<Node> case3incList = ((SimpleNode)iter.jjtGetChild(1)).findChildrenOfType(ASTPrimaryExpression.class);
						if(case3incList == null)																		
							continue;	
						else{
							List<SimpleNode> idInBoth = new ArrayList<SimpleNode>();
							for(Node snode : case3conList){
								ASTPrimaryExpression conId = (ASTPrimaryExpression)snode;
							
								if(conId.getType() instanceof CType_BaseType){
									{
								
										for(Node mnode :case3incList){
											String a = conId.getImage().toString();
											if (conId.getImage().equals(((SimpleNode)mnode).getImage()))
												idInBoth.add(conId);										
										}
									}
								}
							}
								
							if(idInBoth == null)									
								continue;	
							
							if(checkFloat(idInBoth)){
									addFSM(list,iter,fsm);
									break;
									}													
								}
							}	
						
				 break;
			
			case 4 ://for中三个表达式都未省略 
					ASTExpression conditionExp = (ASTExpression)iter.jjtGetChild(1);
					ASTExpression incrementExp = (ASTExpression)iter.jjtGetChild(2);
					
					List<Node> conList = conditionExp.findChildrenOfType(ASTPrimaryExpression.class);
					
					/*条件表达式中无PrimaryExpressio*/
					if (conList == null)
						break;
					
					List<Node> incList = incrementExp.findChildrenOfType(ASTPrimaryExpression.class);
					if(incList == null)						
						break;
										
					/*递增表达式中有PrimaryExpression，选取相同的PrimaryExpression*/
					List<SimpleNode> idInBoth = new ArrayList<SimpleNode>();
					for(Node snode : conList){
						ASTPrimaryExpression conId = (ASTPrimaryExpression)snode;
					
						if(conId.getType() instanceof CType_BaseType){
							{
									
								for(Node mnode :incList){
									String a = conId.getImage().toString();
									if (conId.getImage().equals(((SimpleNode)mnode).getImage()))
										idInBoth.add(conId);										
								}
							}
						}
					}
					if(idInBoth == null)
						break;												
					/*有相同的PrimaryExpression，判断PrimaryExpression是否为实型*/
					if(checkFloat(idInBoth)){
							addFSM(list,iter,fsm);
							break;
						}
			
			default:
					break;
			
			}
		}
		
			
		
		return list;
			
	
  }
	
	
	private static boolean checkFloat(List<SimpleNode> list){
		for(SimpleNode snode :list){
			ASTPrimaryExpression conId = (ASTPrimaryExpression)snode;
			if(conId.getType().toString().equals("float") || conId.getType().toString().equals("double")||conId.getType().toString().equals("long double"))
				return true;
			}
		return false;	
		
	}

	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp("ImproperLoopVariable: Some type is not proper as loop variable,espesialy the float type.");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("禁止使用不合适的循环变量类型: 有许多类型不适合用于循环变量，尤其是实型变量。");
			}	
		
		list.add(fsminstance);
	}
}
