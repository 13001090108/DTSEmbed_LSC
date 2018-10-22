 package softtest.rules.gcc.rule;

import java.util.*;

import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.database.c.*;
import softtest.fsmanalysis.c.CAnalysis;

/**
 * @author 
 * Blank if Branch 4.3.1.1 禁止条件判别成立时相应分支无执行语句
 **/
public class BIBStateMachine
{

	public static List<FSMMachineInstance> createBIBStateMachines(
			SimpleNode node, FSMMachine fsm)
	{
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		String xpath = ".//SelectionStatement[@Image='if']";
		List<SimpleNode> result = StateMachineUtils.getEvaluationResults(node,
				xpath);

		for (Iterator itr = result.iterator(); itr.hasNext();)
		{

			ASTSelectionStatement selNode = (ASTSelectionStatement) itr
					.next();
			if (selNode.jjtGetChild(1) instanceof ASTStatement)
			{
				ASTStatement clause = (ASTStatement) selNode.jjtGetChild(1);
				if (clause.jjtGetChild(0) instanceof ASTExpressionStatement)
				{ // if(a);
					ASTExpressionStatement expr = (ASTExpressionStatement)clause.jjtGetChild(0);
					if(expr.jjtGetNumChildren() == 0)
					{
						addFSM(list, clause, fsm);
						continue;
					}
				}
				else
					if (clause.jjtGetChild(0) instanceof ASTCompoundStatement)
					{
						ASTCompoundStatement comClause = (ASTCompoundStatement) clause.jjtGetChild(0);
						if (comClause.jjtGetNumChildren() == 0)
						{ // if(a){}
							if (isRealBlank(selNode, 2))
							{
								addFSM(list, comClause, fsm);
								continue;
							}
						}
						else
						{ // if(a){;}
							if(comClause.jjtGetChild(0) instanceof ASTStatementList)
							{
								ASTStatementList stalist = (ASTStatementList) comClause.jjtGetChild(0);
								ASTStatement firstClause = (ASTStatement) stalist.jjtGetChild(0);
								if(firstClause.jjtGetChild(0) instanceof ASTExpressionStatement)
								{
									ASTExpressionStatement expr  = (ASTExpressionStatement)firstClause.jjtGetChild(0);
									if(expr.jjtGetNumChildren() == 0)
									{
										if (isRealBlank(selNode, 3))
										{
											addFSM(list, firstClause, fsm);
											continue;
										}
									}
								}
							}
							
						}
					}
			}
		}
		return list;
	}

	/** 汇编代码并无语法树结点，避免误报需分析小段代码 */
	private static boolean isRealBlank(SimpleNode selNode, int condition)
	{
		if( CAnalysis.getCurAnalyElmt() == null)
		{
			return true;
		}
		
		String interFilePath = CAnalysis.getCurAnalyElmt().getInterFileName();
		String sourceCode = DBAccess.getSouceCode(interFilePath, selNode.getBeginFileLine(), selNode.getEndFileLine()); // 消除汇编代码造成的误报，读取源码分析
		sourceCode = sourceCode.replaceAll("\\s", ""); // 去掉所有空白字符
		String[] temp = sourceCode.split("if", 2); // 嵌套的if呢
		if (temp.length == 2)
			sourceCode = temp[1]; // 取得if后面的代码
		else
			sourceCode = temp[0]; // ？？？
		switch (condition)
		{
			case 1:
				int count = 1;
				int index = 0;
				for (int i = sourceCode.indexOf("(") + 1; i < sourceCode
						.length(); i++)
				{ // for：括号匹配
					if (sourceCode.charAt(i) == '(')
						count++;
					if (sourceCode.charAt(i) == ')')
						count--;
					if (count == 0)
					{
						index = i;
						break;
					}
				}
				if (index <= sourceCode.length() - 2
						&& sourceCode.charAt(index + 1) == ';')
					return true;
				else
					return false;
			case 3:
				sourceCode = sourceCode.replaceAll(";", ""); // 把case3归结为case2
			case 2:
				if (sourceCode.indexOf("{") == sourceCode.length() - 1)
					return false;
				if (sourceCode.charAt(sourceCode.indexOf("{") + 1) == '}')
					return true;
				else
					return false;
		}
		return true;
	}

	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node,FSMMachine fsm)
	{
		FSMMachineInstance fsmInstance = fsm.creatInstance();
		fsmInstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH)
			fsmInstance.setDesp("There is a blank if branch in line "
					+ node.getBeginLine() + ".In order to avoid "
					+ "the mistake, so don't use a blank branch.");
		else
			if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
				fsmInstance.setDesp("在第 " + node.getBeginLine()
						+ " 行出现了if语句的空分支。"
						+ "为了防止由于疏忽造成的遗漏，因此禁止条件判别成立时相应分支无执行语句。");
		list.add(fsmInstance);
	}
}
