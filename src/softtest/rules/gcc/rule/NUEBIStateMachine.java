package softtest.rules.gcc.rule;

import java.util.*;

import softtest.ast.c.ASTExpression;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTSelectionStatement;
import softtest.ast.c.ASTStatement;
import softtest.ast.c.ASTStatementList;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.VexNode;
import softtest.config.c.Config;
import softtest.database.c.DBAccess;
import softtest.domain.c.analysis.ConditionData;
import softtest.domain.c.analysis.SymbolDomainSet;
import softtest.domain.c.analysis.ValueSet;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.DomainType;
import softtest.domain.c.interval.DoubleDomain;
import softtest.domain.c.interval.IntegerDomain;
import softtest.domain.c.interval.PointerDomain;
import softtest.domain.c.symbolic.Expression;
import softtest.domain.c.symbolic.SymbolFactor;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.VariableNameDeclaration;

/**
 * @author Not Use else Between if 4.3.1.2 在if…else if 语句中必须使用else分支
 **/
public class NUEBIStateMachine
{

	public static List<FSMMachineInstance> createNUEBIStateMachines(SimpleNode node, FSMMachine fsm)
	{
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		String xpath = ".//SelectionStatement[@Image='if']";
		List<SimpleNode> result = StateMachineUtils.getEvaluationResults(node,xpath);

		for (Iterator itr = result.iterator(); itr.hasNext();)
		{
			ASTSelectionStatement sel1 = (ASTSelectionStatement) itr.next();
			SimpleNode statement = null; // selection结点的最上层statment结点
			int num = 0; // 记录statement结点是第几个孩子
			ASTStatement statementBrother = null;
			if (sel1.jjtGetNumChildren() == 3) // if语句带有else分支
				continue;
			
			statement = (SimpleNode) sel1.jjtGetParent(); // while？？？
			while (!(statement.jjtGetParent() instanceof ASTStatementList))
			{
				statement = (SimpleNode) statement.jjtGetParent();
			}
			ASTStatementList statelist = (ASTStatementList) statement.jjtGetParent();
			for (int i = 0; i < statelist.jjtGetNumChildren(); i++)
			{
				if (statelist.jjtGetChild(i).equals(statement))
				{
					num = i;
					break;
				}
			}
			if (num == statelist.jjtGetNumChildren() - 1)
				continue;
			else
			{
				statementBrother = (ASTStatement) statelist.jjtGetChild(num + 1);
				ASTSelectionStatement sel2 = null;
				if (statementBrother.jjtGetNumChildren() == 1
						&& statementBrother.jjtGetChild(0) instanceof ASTSelectionStatement)
				{
					sel2 = (ASTSelectionStatement) statementBrother.jjtGetChild(0);
					ASTExpression exp1 = (ASTExpression) sel1.jjtGetChild(0);
					ASTExpression exp2 = (ASTExpression) sel2.jjtGetChild(0);
					VexNode vex1 = exp1.getCurrentVexNode();
					VexNode vex2 = exp2.getCurrentVexNode();
					if (vex1 != null && vex2 != null)
					{
						ValueSet vs1 = vex1.getValueSet();
						ValueSet vs2 = vex2.getValueSet();
						int i = vs1.getTable().keySet().size();
						int j = vs2.getTable().keySet().size();
						if(i != j)
						{
							break;
						}
						
						ConditionData data1 = vex1.getCondata();
						ConditionData data2 = vex2.getCondata();
						if(data1 == null || data2 == null)
						{
							break;
						}
						
						SymbolDomainSet false1Symbol = data1.getFalseMustDomainSet();
						SymbolDomainSet true2Symbol = data2.getTrueMayDomainSet();
						
						Enumeration en = vs1.getTable().keys();
						boolean flag = true;
						while(en.hasMoreElements())
						{
							VariableNameDeclaration varDecl = (VariableNameDeclaration)en.nextElement();
							
							if(vs2.getTable().containsKey(varDecl) == false)
							{
								flag = false;
								break;
							}
							
							Expression false1Expression = vs1.getTable().get(varDecl);
							Expression true2Expression = vs2.getTable().get(varDecl);
							
							Domain false1Domain = false1Expression.getDomain(false1Symbol);
							Domain true2Domain = true2Expression.getDomain(true2Symbol);
							if(false1Domain == null || true2Domain == null)
							{
								flag = false;
								break;
							}
							
							DomainType true2Type = true2Domain.getDomaintype();
							DomainType false1Type = false1Domain.getDomaintype();
							if (false1Type != true2Type)
							{
								flag = false;
								break;
							}
							Domain ret = null;
							switch (false1Type)
							{
								case POINTER:
									{
										PointerDomain p1 = (PointerDomain) false1Domain;
										PointerDomain p2 = (PointerDomain) true2Domain;
										ret = PointerDomain.intersect(p1, p2);
										break;
									}
								case INTEGER:
									{
										IntegerDomain i1= (IntegerDomain) false1Domain;
										IntegerDomain i2 = (IntegerDomain) true2Domain;
										ret = IntegerDomain.intersect(i1, i2);
										break;
									}
								case DOUBLE:
									{
										DoubleDomain d1 = (DoubleDomain) false1Domain;
										DoubleDomain d2 = (DoubleDomain) true2Domain;
										ret = DoubleDomain.intersect(d1, d2);
										break;
									}
								case UNKNOWN:
								default:
									break;
							}
							if (ret == null || Domain.isEmpty(ret))
							{
								flag = false;
								break;
							}
						}// while
						if (flag == true)
						{
							addFSM(list, sel1, sel2, fsm);
						}
					}
				}
			}
		}
		return list;
	}

	/** 判断两个if的谓词表达式，若两个涉及的表达式相同，返回true */
	private static boolean haveSameIdexpression(List idList1, List idList2)
	{
		if (idList1.size() != idList2.size())
			return false;
		List<String> nameList1 = new ArrayList<String>(), nameList2 = new ArrayList<String>();
		for (int i = 0; i < idList1.size(); i++)
		{
			ASTPrimaryExpression id1 = (ASTPrimaryExpression) idList1.get(i), id2 = (ASTPrimaryExpression) idList2
					.get(i);
			nameList1.add(id1.getImage());
			nameList2.add(id2.getImage());
		}
		Collections.sort(nameList1);
		Collections.sort(nameList2);
		for (int i = 0; i < nameList1.size(); i++)
		{
			if (!nameList1.get(i).equals(nameList2.get(i)))
				return false;
		}
		return true;
	}

	//
	private static boolean haveSameCode(ASTExpression exp1, ASTExpression exp2)
	{
		String code1 = DBAccess.getSouceCode(exp1.getFileName(), exp1
				.getBeginLine(), exp1.getBeginColumn(), exp1.getEndLine(), exp1
				.getEndColumn());
		String code2 = DBAccess.getSouceCode(exp2.getFileName(), exp2
				.getBeginLine(), exp2.getBeginColumn(), exp2.getEndLine(), exp2
				.getEndColumn());
		if (code1.startsWith("!") && code2.startsWith("!"))
			return true; // 两个都判断假加else会改变语义,不报
		if (code1.contains("!=") && code2.contains("!="))
			return true;
		if (code1.replaceAll("\\s", "").equals(code2.replaceAll("\\s", "")))
			return true;
		return false;
	}

	private static void addFSM(List<FSMMachineInstance> list,
			SimpleNode selNode, SimpleNode node, FSMMachine fsm)
	{
		FSMMachineInstance fsmInstance = fsm.creatInstance();
		fsmInstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH)
			fsmInstance
					.setDesp("Not use else between if in line "
							+ selNode.getBeginLine()
							+ "and "
							+ node.getBeginLine()
							+ ". In order to show"
							+ " that all possibilities are already being concerned, so else branch is recommanded to use.");
		else
			if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
				fsmInstance.setDesp("在第 " + selNode.getBeginLine() + " 行和第"
						+ node.getBeginLine() + "行的if语句之间没有使用else。"
						+ "在if…else if语句中为了表明已经考虑了所有情况，必须使用else分支。");
		list.add(fsmInstance);
	}
}
