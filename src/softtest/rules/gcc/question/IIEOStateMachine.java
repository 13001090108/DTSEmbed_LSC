package softtest.rules.gcc.question;


import java.util.*;

import softtest.ast.c.ASTArgumentExpressionList;
import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTAssignmentOperator;
import softtest.ast.c.ASTDeclarator;
import softtest.ast.c.ASTExpression;
import softtest.ast.c.ASTPostfixExpression;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.ASTUnaryOperator;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.Type.CType;
import softtest.symboltable.c.Type.CType_Array;
import softtest.symboltable.c.Type.CType_Pointer;



/** 
 * @author chh
 * IIEO 循环条件中隐藏的低效操作
 */
public class IIEOStateMachine {
	
	public static List<FSMMachineInstance> createIIEOStateMachines(SimpleNode node, FSMMachine fsm) {
		String iteration_xpath = ".//Statement/IterationStatement";
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
		
		evaluationResults = StateMachineUtils.getEvaluationResults(node, iteration_xpath);
		if(evaluationResults == null)
			return null;
		for(SimpleNode iterator : evaluationResults) {
			
			//循环语句中出现自定义函数
			doFunctionSpecial(iterator, fsm, list);
		}
	    return list;
	}	
	
	/*
	 * node : ASTiteration_statment
	 */
	private static void doFunctionSpecial(SimpleNode iterator, FSMMachine fsm, List<FSMMachineInstance> list) {
		String xpath = "./Expression/AssignmentExpression/RelationalExpression//UnaryExpression/PostfixExpression/PrimaryExpression[@Method='true']";
		List<SimpleNode> results = StateMachineUtils.getEvaluationResults(iterator, xpath);	
		//step1： 确保循环语句中的条件判断语句中有函数存在
		if(results == null || results.size() != 1)
			return ;
		ASTPrimaryExpression snode = (ASTPrimaryExpression)results.get(0); 
		if(snode.jjtGetParent().jjtGetNumChildren()==1)
			return;
		SimpleNode args = (SimpleNode) snode.jjtGetParent().jjtGetChild(1);
		if(args == null)
			return ;
		List<SimpleNode> argList = StateMachineUtils.getEvaluationResults(args, "./AssignmentExpression");
		//step2: 仅处理参数个数为1的函数
		if(argList == null || argList.size() != 1 )
			return ;
		//除去func(*a),func(&a)该类型参数
		String argXpath = "./AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression";
		argList = StateMachineUtils.getEvaluationResults(args, argXpath);	
		if(argList == null || argList.size() != 1)
			return ;
		SimpleNode node = argList.get(0); 
		//step3: 得到当前函数的参变量类型（支持char[] char *两种）
		VariableNameDeclaration variable = node.getVariableNameDeclaration();
		if(variable == null || variable.getType() == null)
			return ;	
		CType type = variable.getType();
		if(!(( type instanceof CType_Pointer ||  type instanceof CType_Array ) && CType.getOrignType(type).getName().equals("char")))
			return ;
		//step4: 判断当前循环node中variable是不是被改变
		if(checkNoChange(variable, iterator)) {
		
			addFSMDesp(node, variable, fsm, list);
		}
	}



	/**
	 * 判断循环语句中出现的所有变量，如果和传入的参数Variable是同一个变量，进入isChange()方法再判断
	 * @param 变量声明
	 * @param iteration节点
	 * @return 如果当前循环节点node中variable没有改变，返回true；否则返回false
	 * */
	private static boolean checkNoChange(VariableNameDeclaration variable, SimpleNode ancestor) {
		String xpath = "./Statement//PrimaryExpression ";
		List<SimpleNode> results = null;
		results = StateMachineUtils.getEvaluationResults(ancestor, xpath);
		Iterator itr = results.iterator();
		while(itr.hasNext()) {
			SimpleNode snode = (SimpleNode) itr.next();
			if(snode.getVariableNameDeclaration()!= null && snode.getVariableNameDeclaration() == variable) {	
				if(isChange(snode,ancestor))
					return false;	
			}
		}
		return true;
	}

	/**
	 * str=“acf”;
	 * func(&str);
	 * i = func(&str);
	 * &str = cc;
	 * func(str);
	 * 仅上述五种情况算是改变了str
	 * *str='a';
	 * str[2]='a';
	 * 上述两种情况均不算改变了str
	 * */
	private static boolean isChange(SimpleNode node, SimpleNode ancestor) {
		
		SimpleNode parent = (SimpleNode) node.jjtGetParent();
		
		//1.判断func(&str)类型
		SimpleNode arg = (SimpleNode) node.getFirstParentOfType(ASTArgumentExpressionList.class);
		if(arg != null && arg.jjtGetChild(0).jjtGetChild(0).jjtGetNumChildren()==2) {	
			SimpleNode ptr = (SimpleNode) arg.jjtGetChild(0).jjtGetChild(0).jjtGetChild(0);
			if(ptr.getOperators().equals("&")) {	
				//System.out.println("------------------类型func(&str)");
				return true;
			}
			if(ptr.getOperators().equals("*")) {	
				//System.out.println("------------------类型func(*str)");
				return false;
			}
		}
		
		
		//2.除去str[0]类型
		
		if(parent instanceof ASTPostfixExpression && parent.jjtGetNumChildren() == 2) {	
			if(parent.jjtGetChild(1) instanceof ASTExpression) {	
				//System.out.println("------------------除去类型str[2]");
				return false;
			}
		}
		else {
			parent = (SimpleNode) node.getFirstParentOfType(ASTUnaryExpression.class);
		}
		
		if(arg != null && arg.jjtGetChild(0).jjtGetChild(0).jjtGetNumChildren()==1) {	
			return true;
		}
		
		//3.判断i=func(&str)类型 或者&str=cc类型
		
		if(parent!= null && parent.jjtGetParent() instanceof ASTUnaryExpression && parent.jjtGetParent().jjtGetNumChildren()==2) {
			SimpleNode child = (SimpleNode) parent.jjtGetParent().jjtGetChild(0);
			if(child instanceof ASTUnaryOperator && child.getImage().equals("&")) {
				//System.out.println("------------------类型&str");
				return true;
			}
			if(child instanceof ASTUnaryOperator && child.getImage().equals("*")) {
				//System.out.println("------------------类型*str");
				return false;
			}
				
		}
		
		//通过123过滤后，就剩下str类型。
		//4.判断str是否位于赋值表达式的左边str="avc"
		// 而str[0]='a'不算
		
		if(parent.jjtGetParent() instanceof ASTAssignmentExpression && parent.jjtGetParent().jjtGetNumChildren()==3) {
			parent = (SimpleNode) parent.jjtGetParent();
			
			if(parent.jjtGetChild(1)!=null && ((ASTAssignmentOperator)parent.jjtGetChild(1)).getOperators().equals("=")) {
				//System.out.println("------------------类型str=");
				return true;
			}
		}	
				
		return false;
	}
	
	private static void addFSMDesp(SimpleNode node, VariableNameDeclaration variable, FSMMachine fsm, List<FSMMachineInstance> list) {	
		FSMMachineInstance fsminstance = fsm.creatInstance();		
		fsminstance.setRelatedASTNode(node);
		fsminstance.setRelatedVariable(variable);
		
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH)
			fsminstance.setDesp("Inefficient operation exists in loop statement.");
		else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
			fsminstance.setDesp("第"+node.getBeginLine()+"行：循环条件中隐藏的低效操作。\r\n如果循环条件中有一个函数调用，该函数的返回值是不会在循环条件中改变的，一定要把它放置于循环外。");	
		
		list.add(fsminstance);
	}
}

