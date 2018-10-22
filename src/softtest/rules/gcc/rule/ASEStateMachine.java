package softtest.rules.gcc.rule;

import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.Node;
import softtest.ast.c.SimpleNode;
import softtest.ast.c.ASTIterationStatement;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;

/**
 * @author xiangwentao
 * Avoid Some Expression
 * 谨慎使用三重表达式/避免使用空语句/避免使用不起作用的语句/避免使用continue语句  (推荐类)
 * (语句使用类)
 */

public class ASEStateMachine {
	private enum Type {TYPE_1, TYPE_2, TYPE_3, TYPE_4};
	
	//查询三重表达式
	private static final String xPath_1 = ".//ConditionalExpression[count(child::*)=3 and ./UnaryExpression] ";
	//查询空语句
	private static final String xPath_2 = ".//Statement[@EndColumn=@BeginColumn and ./ExpressionStatement] ";
	//查询所有不起作用的语句
	private static final String xPath_3 = ".//Statement/ExpressionStatement/Expression/AssignmentExpression[count(*)=1 and ./UnaryExpression[count(*)=1]] ";
	//查询continue语句
	private static final String xPath_4 = ".//Statement[./JumpStatement[@Image='continue']] ";
	
	public static List<FSMMachineInstance> createASEMachines(SimpleNode node, FSMMachine fsm){
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();	
		List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
		
		//Type.first_type 查询所有三重表达式,如x==0?f1():f2();
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath_1);
		for(SimpleNode snode : evaluationResults) {
			addFSM(snode, fsm, Type.TYPE_1, list);
		}
		
		//Type.second_type 查询所有空语句
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath_2);
		for(SimpleNode snode : evaluationResults) {
			addFSM(snode, fsm, Type.TYPE_2, list);
		}
		
		//Type.third_type 查询所有使用不起作用的语句,如x;
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath_3);
		for(SimpleNode snode : evaluationResults) {
			ASTUnaryExpression UnaryExp = (ASTUnaryExpression)snode.jjtGetChild(0);
			if(UnaryExp.getOperators().length() == 0 ){
				SimpleNode PostfixExp = (SimpleNode)UnaryExp.jjtGetChild(0);
				if(PostfixExp.getOperators().length() == 0 && PostfixExp.jjtGetNumChildren() == 1){
					SimpleNode PrimaryExp = (SimpleNode)PostfixExp.jjtGetChild(0);
					if(PrimaryExp.jjtGetNumChildren() == 0)
			            addFSM(snode, fsm, Type.TYPE_3, list);
				}
			}
		}
	    
	    //Type.fourth_type 查询所有continue语句
	    evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath_4);
		for(SimpleNode snode : evaluationResults) {
			if(isIterationEnd(snode,node))
				addFSM(snode, fsm, Type.TYPE_4, list);
		}
	    return list;
	}
	
	/**
	 * @param ASTstatement
	 * @return 如果该语句为循环语句的最后一句，返回true;否则返回false
	 */
	private static boolean isIterationEnd(SimpleNode snode,Node node) {

		SimpleNode child = snode;
		SimpleNode iteration = (SimpleNode) child.getFirstParentOfType(ASTIterationStatement.class,node);
		if(iteration == null)
			return false;
		SimpleNode parent = (SimpleNode)snode.jjtGetParent();
		if(iteration.getImage().equals("while") || iteration.getImage().equals("for")) {
			do{
				int index = parent.jjtGetNumChildren()-1;
				if(parent.jjtGetChild(index) != child)
					return false;
				child = parent;
				parent = (SimpleNode)child.jjtGetParent();
			}while(parent != iteration);
		}
		else if(iteration.getImage().equals("do")) { //对于do-while循环
			iteration = (SimpleNode)iteration.jjtGetChild(0); //do-while的话，针对它的第一个子节点，即ASTstatement
			do{
				int index = parent.jjtGetNumChildren()-1;
				if(parent.jjtGetChild(index) != child)
					return false;
				child = parent;
				parent = (SimpleNode)child.jjtGetParent();
			}while(parent != iteration);
		}
		return true;
	}
	
	private static void addFSM(SimpleNode node, FSMMachine fsm, Type type, List<FSMMachineInstance> list) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		
		if(type == Type.TYPE_1) {
			if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
					fsminstance.setDesp("Avoid using Triple Expressions. It will reduce the readabilty of the code.");
				} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
					fsminstance.setDesp("谨慎使用三重表达式。\r\n三重表达式的使用会降低程序的可读性，容易出现编程失误。");
				}	
		}		
		else if(type == Type.TYPE_2) {
			if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp("Avoid using empty statement. Some compiler couldn't handle empty statement, so it is recommended to avoid using it.");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("避免使用空语句。\r\n有些编译器是不能处理空语句的，所以建议避免使用空语句。");
			}
		}	
		else if(type == Type.TYPE_3) {
			if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp("Avoid using useless expression.It has no effect of the context, it belongs to useless statement.");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("避免使用不起作用的语句。\r\n如果语句没有改变局部变量或全局变量的值，也没有影响控制流，那么这些语句为冗余语句。");
			}
		}
		else if(type == Type.TYPE_4) {
			if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp("Avoid using continue expression. Sometimes the use of continue statement will lead to a meaningless programm code. ");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("避免使用continue语句。\r\n语句continue的使用有时会导致无实际意义的程序代码，应避免使用。");
			}
		}
		list.add(fsminstance);
	}
}


