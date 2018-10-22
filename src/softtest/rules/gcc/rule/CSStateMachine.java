package softtest.rules.gcc.rule;

import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.fsm.c.FSMRelatedCalculation;



/**
 * @author 
 * @CS means const string
 * @禁止字符串中单独使用“\”，字符串的终止必须使用“\0”
 */
public class CSStateMachine
{
	public static List<FSMMachineInstance> createCSStateMachines(SimpleNode node, FSMMachine fsm)
	{
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		String xPath = ".//PostfixExpression/PrimaryExpression/Constant";
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);
		for (SimpleNode snode : evaluationResults)
		{
			FSMMachineInstance fsminstance = fsm.creatInstance();
			fsminstance.setRelatedASTNode(snode);
			fsminstance.setRelatedObject(new FSMRelatedCalculation(snode));
			list.add(fsminstance);
		}
		return list;
	}

	public static boolean checkHasSpecialChar(List<SimpleNode> nodes,FSMMachineInstance fsmin)
	{
		boolean result = false;
		SimpleNode simnode = fsmin.getRelatedASTNode();
		for (SimpleNode node : nodes)
		{
			if (simnode != node)
				continue;
			String str = node.getImage();
			for (int i = 0; i < str.length() - 1; i++)
			{
				if (str.substring(i, i + 1).equals("\\"))
				{
					if (str.substring(i + 1, i + 2).equals("\n"))
					{
						result = true;
						addFSMDescription(fsmin);
					}
				}
			}
		}
		return result;
	}

	private static void addFSMDescription(FSMMachineInstance fsminstance)
	{

		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH)
		{
			fsminstance.setDesp(" Const string use a single \\  ");
		}
		else
			if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
			{
				fsminstance.setDesp("常量字符串中使用了单个的 \\");
			}
	}
}
