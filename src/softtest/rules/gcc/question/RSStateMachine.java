package softtest.rules.gcc.question;

import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.ASTJumpStatement;
import softtest.ast.c.ASTLabeledStatement;
import softtest.ast.c.ASTSelectionStatement;
import softtest.ast.c.ASTStatement;
import softtest.ast.c.ASTStatementList;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
/** 
 * @author ssj
 */
public class RSStateMachine {
	
	public static List<FSMMachineInstance> createRedundanceStatementMachines(SimpleNode node, FSMMachine fsm){	
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		
		//找return/break/continue之后紧跟的冗余语句
		createRedundanceStatement1(node, fsm, list);	
		//特殊处理：找到条件判断语句中的冗余语句
		doSelectionSpecial(node, fsm, list);
		//特殊处理： switch语句
		doSwitchSpecial(node, fsm, list);
		//特殊处理： 循环语句最后一条语句为return( 如果是if语句的话，满足ifAllReturn()条件)
		doIterationSpecial(node, fsm, list);
	    return list;
	}
	
	/**
	 * 特殊处理： 循环语句最后一条语句为return
	 */
	private static void doIterationSpecial(SimpleNode node, FSMMachine fsm, List<FSMMachineInstance> list) {
		//找到循环语句(最后一条语句为return)
		String iterationXpath = "//Statement[./IterationStatement/Statement/CompoundStatement/StatementList/Statement[last()]/JumpStatement[@Image='return']]";
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, iterationXpath);
		if(evaluationResults == null)
			return ;
		for(SimpleNode snode : evaluationResults) {
			String xPath = ".//JumpStatement[Image='continue' or @Image='break']";
			List<SimpleNode> jumpResults = StateMachineUtils.getEvaluationResults(snode, xPath);
			if(jumpResults != null){
				continue;
			}
			SimpleNode next = findNextStatement((ASTStatement)snode);
			if(next!=null  && next.jjtGetNumChildren() >= 1 && !(next.jjtGetChild(0) instanceof ASTLabeledStatement))
				addFSMDesp(next, fsm, list);
		}
	}

	/**
	 * Find the statement after this return statement
	 */
	private static SimpleNode findNextStatement(ASTStatement node) {
		SimpleNode parent = (SimpleNode) node.jjtGetParent();
		if(!(parent instanceof ASTStatementList))
			return null;
		int index = 0;
		for(index=0; index<parent.jjtGetNumChildren(); index++) {
			if(parent.jjtGetChild(index) == node) 
				break;
		}
		index++;
		if(index<parent.jjtGetNumChildren()) {
			SimpleNode next = (SimpleNode) parent.jjtGetChild(index);
			return next;
		}
		return null;
	}

	/**
	 * 特殊处理switch语句，所有的标记都有return语句
	 */
	private static void doSwitchSpecial(SimpleNode node, FSMMachine fsm, List<FSMMachineInstance> list) {
		String xpath =".//Statement/SelectionStatement[@Image='switch']";
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		if(evaluationResults == null)
			return ;
		for(SimpleNode switchNode : evaluationResults) {
			//step1： switch是否含有default标记节点，无default不用继续
			String defaultXpath ="./Statement/CompoundStatement/StatementList/Statement[./LabeledStatement[@Image='default']]";
			List<SimpleNode> results = StateMachineUtils.getEvaluationResults(switchNode, defaultXpath);
			if(results == null || results.size()==0)
				continue;
			//step2： 找到switch语句所有的标记节点，对于每个标记节点，判断是否有return语句
			String labelXpath ="./Statement/CompoundStatement/StatementList/Statement[./LabeledStatement[@Image='case' or @Image='default']]";
			List<SimpleNode> labelResults = StateMachineUtils.getEvaluationResults(switchNode, labelXpath);
			for(SimpleNode label : labelResults) {
				//state1: 标记之后紧跟if语句
				if(label.getFirstChildOfType(ASTSelectionStatement.class) != null) {
					SimpleNode snode = (SimpleNode) label.getFirstChildOfType(ASTSelectionStatement.class); 
					if(isAllReturn(snode))
						continue;
				} 
				//state2:　标记之后紧跟return语句
				else if(label.getFirstChildOfType(ASTJumpStatement.class) != null) { 
					if(((SimpleNode)label.getFirstChildOfType(ASTJumpStatement.class)).getImage().equals("return"))
						continue;
					else  //该标记下无return语句 
						return ; 
				}
				//state３: 标记之后跟return语句(不过不是紧跟标号之后)
				SimpleNode parent = (SimpleNode) label.jjtGetParent();
				int index = 0;
				for(index=0; index<parent.jjtGetNumChildren(); index++) {
					if(parent.jjtGetChild(index) == label) {
						break ;
					}
				}
				//找到标记语句之后的下条语句
				while(index+1 < parent.jjtGetNumChildren()) {
					index++;
					SimpleNode next = (SimpleNode) parent.jjtGetChild(index);
					if(next.getFirstChildOfType(ASTLabeledStatement.class) != null)  //next为该标记节点
						return ; 
					
					//state3.1: 标记之后紧跟if语句
					if(next.getFirstChildOfType(ASTSelectionStatement.class) != null) {
						SimpleNode snode = (SimpleNode) next.getFirstChildOfType(ASTSelectionStatement.class); 
						if(isAllReturn(snode))
							break;
					} 
					//state3.2: 标记之后无if语句
					else if(next.getFirstChildOfType(ASTJumpStatement.class) != null) {
						if(((SimpleNode)next.getFirstChildOfType(ASTJumpStatement.class)).getImage().equals("return"))
							break;
						else if(((SimpleNode)next.getFirstChildOfType(ASTJumpStatement.class)).getImage().equals("break"))
							return ;
					}
				}
			}
			//得到switch语句的父节点
			ASTStatement curNode = (ASTStatement) switchNode.jjtGetParent();
			SimpleNode next = findNextStatement(curNode);
			if(next != null  && next.jjtGetNumChildren() > 0 && !(next.jjtGetChild(0) instanceof ASTLabeledStatement))
				addFSMDesp(next, fsm, list);
		}
	}

	/*
	 * 找return/break/continue之后紧跟的冗余语句
	 */
	private static void createRedundanceStatement1(SimpleNode node, FSMMachine fsm, List<FSMMachineInstance> list) {
		//找到所有的break语句、continue语句和return语句 
		String xpath =".//Statement[./JumpStatement[@Image='return' or @Image='break' or @Image='continue']] ";
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		for (SimpleNode snode : evaluationResults) {
			SimpleNode presnode = snode;
			if(snode.jjtGetParent() instanceof ASTLabeledStatement)
				snode = (SimpleNode) snode.jjtGetParent().jjtGetParent();
			
			//找到了当前snode节点，然后find是否该节点后有兄弟节点，如果有，而且是ASTLabeledStatement类型,不能加入到list中
			SimpleNode next = findNextStatement((ASTStatement)snode);
			if(next == null || next.jjtGetNumChildren() < 1)
				continue;
			SimpleNode child = (SimpleNode) next.jjtGetChild(0);
			if(child instanceof ASTLabeledStatement && (child.getImage().equals("case") || child.getImage().equals("default")))
				continue;
			else if(((SimpleNode)presnode.jjtGetChild(0)).getImage().equals("return") && child instanceof ASTLabeledStatement) //特殊处理return之后，有标号语句，而该标号是之前goto label1中应当定义的.
				continue;
			else
				addFSMDesp(child, fsm, list);
		}
	}


	/*
	 * 如果条件判断语句的分支中，如果都有返回退出语句，则后面语句就属多余语句
	 */
	public static void doSelectionSpecial(SimpleNode node, FSMMachine fsm, List<FSMMachineInstance> list) {
		//找到所有的if语句
		String xpath =".//SelectionStatement[@Image='if']";
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		if(evaluationResults == null || evaluationResults.size()==0)
			return ;
		for (SimpleNode snode : evaluationResults) {
			if(isAllReturn(snode)) {
				SimpleNode parent = (SimpleNode) snode.jjtGetParent(); //得到Statement节点
				SimpleNode  ancestor = (SimpleNode) parent.jjtGetParent();//打算得到snode的祖父节点StatementList
				while(!(ancestor instanceof ASTStatementList)) {
					parent = ancestor;
					ancestor = (SimpleNode) parent.jjtGetParent();
				}
				//该if语句之后还有节点,得到if语句的next语句
				SimpleNode next = findNextStatement((ASTStatement) parent);
				if(next != null &&  next.jjtGetNumChildren() >= 1 && !(next.jjtGetChild(0) instanceof ASTLabeledStatement)) { //如果if之后是case语句，不能报
					addFSMDesp(next, fsm, list);
				}
			}
		}
	}
	
	/*
	 * @param ASTSelectionStatement
	 * 判断该节点所有语句是否均有返回值
	 */
	private static boolean isAllReturn(SimpleNode snode) {
		if(snode.jjtGetNumChildren() < 3)//如果if语句没有if-else分支的话
			return false;		
		SimpleNode ifchild = (SimpleNode) snode.jjtGetChild(1);
		SimpleNode elsechild = (SimpleNode) snode.jjtGetChild(2);
		if(ifchild.jjtGetNumChildren()> 0 && ifchild.jjtGetChild(0) instanceof ASTSelectionStatement && !isAllReturn(ifchild))
			return false;	
		if(elsechild.jjtGetNumChildren()> 0 && elsechild.jjtGetChild(0) instanceof ASTSelectionStatement && !isAllReturn(elsechild))
			return false;

		String hasReturn = "./JumpStatement[@Image='return'] | ./CompoundStatement/StatementList/Statement/JumpStatement[@Image='return']";
		List  ifResult = StateMachineUtils.getEvaluationResults(ifchild, hasReturn);
		List elseResult = StateMachineUtils.getEvaluationResults(elsechild, hasReturn);
		if( ifResult == null || elseResult == null )
			return false;
		if( ifResult.isEmpty()!=true && elseResult.isEmpty()!=true ) 
			return true;
		return false;
	}


	private static void addFSMDesp(SimpleNode node, FSMMachine fsm, List<FSMMachineInstance> list) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp(" This Line belongs to resudance statement which is after return, break or continue statement. This code belongs to dead code.");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("第"+node.getBeginLine()+" 行为return、break、continue语句后的冗余语句。\r\n该语句不会被执行，即死码。");
			}	
		list.add(fsminstance);
	}
}
