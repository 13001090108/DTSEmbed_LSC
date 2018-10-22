package softtest.rules.gcc.rule;

import java.util.*;

import softtest.ast.c.ASTCompoundStatement;
import softtest.ast.c.ASTExpressionStatement;
import softtest.ast.c.ASTSelectionStatement;
import softtest.ast.c.ASTStatement;
import softtest.ast.c.ASTStatementList;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.database.c.DBAccess;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.fsmanalysis.c.CAnalysis;
import softtest.rules.c.StateMachineUtils;

/**
 * @author Blank else 
 * Branch 4.3.1.3 禁止条件判别的else分支无可执行语句
 **/
public class BEBStateMachine
{

	public static List<FSMMachineInstance> createBEBStateMachines(SimpleNode node, FSMMachine fsm)
	{
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		String xpath = ".//SelectionStatement[@Image='if']";
		List<SimpleNode> result = StateMachineUtils.getEvaluationResults(node,
				xpath);

		for (Iterator itr = result.iterator(); itr.hasNext();)
		{
			ASTSelectionStatement selNode = (ASTSelectionStatement) itr
					.next();
			ASTStatement elseClause = null;
			if (selNode.jjtGetNumChildren() != 3) // if语句没有else分支
				continue;
			else
			{
				elseClause = (ASTStatement) selNode.jjtGetChild(2);
				if(elseClause.jjtGetChild(0) instanceof ASTExpressionStatement)
				{
					ASTExpressionStatement expr = (ASTExpressionStatement)elseClause.jjtGetChild(0);
					if(expr.jjtGetNumChildren() == 0)
					{
						if (isRealBlank(elseClause, 1))
						{
							addFSM(list, elseClause, fsm);
							continue;
						}
					}
				}
				else
					if (elseClause.jjtGetChild(0) instanceof ASTCompoundStatement)
					{
						ASTCompoundStatement comClause = (ASTCompoundStatement) elseClause.jjtGetChild(0);
						if (comClause.jjtGetNumChildren() == 0)
						{ // else{}
							if (isRealBlank(elseClause, 2))
							{
								addFSM(list, comClause, fsm);
								continue;
							}
						}
						else
						{ // else{;}
							if(comClause.jjtGetChild(0) instanceof ASTStatementList)
							{
								ASTStatementList stalist = (ASTStatementList) comClause.jjtGetChild(0);
								ASTStatement firstClause = (ASTStatement) stalist.jjtGetChild(0);
								if(firstClause.jjtGetChild(0) instanceof ASTExpressionStatement)
								{
									ASTExpressionStatement expr  = (ASTExpressionStatement)firstClause.jjtGetChild(0);
									if(expr.jjtGetNumChildren() == 0)
									{
//										if (isRealBlank(elseClause, 3))
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

	private static boolean isRealBlank(SimpleNode elseClause, int condition)
	{
		
		if( CAnalysis.getCurAnalyElmt() == null)
		{
			return true;
		}
		
		String interFilePath = CAnalysis.getCurAnalyElmt().getInterFileName();
		String sourceCode = DBAccess.getSouceCode(interFilePath, elseClause.getBeginFileLine(), elseClause.getEndFileLine()); // 消除汇编代码造成的误报，读取源码分析
		sourceCode = sourceCode.replaceAll("\\s", ""); // 去掉所有空白字符
		String[] temp = sourceCode.split("else", 2);
		if (temp.length == 2)
			sourceCode = temp[1]; // 取得else后面的代码
		else
			sourceCode = temp[0];
		switch (condition)
		{
			case 1:
				if (sourceCode.startsWith(";"))
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

	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node,
			FSMMachine fsm)
	{
		FSMMachineInstance fsmInstance = fsm.creatInstance();
		fsmInstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH)
			fsmInstance.setDesp("There is a blank else branch in line "
					+ node.getBeginLine() + ".");
		else
			if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
				fsmInstance
						.setDesp("在第 "
								+ node.getBeginLine()
								+ " 行出现了else语句的空分支。"
								+ "else分支中无可执行语句或是由于代码不完整造成的，或是有意表明 else 对应的可能性已经考虑到了。为了防止残留不完整的代码，因此禁止条件判别的 else分支无可执行语句。");
		list.add(fsmInstance);
	}
}
