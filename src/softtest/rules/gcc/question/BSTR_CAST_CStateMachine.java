package softtest.rules.gcc.question;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.ASTTypeName;
import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.AbstractExpression;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.Type.CType;

/*
 * author:Wangjing
 * 将不满足BSTR特性的指针赋为BSTR型可能引起内存使用的问题。
 * 
 * */
public class BSTR_CAST_CStateMachine {

	static List<SimpleNode> ls = new ArrayList<SimpleNode>();

	public static List<FSMMachineInstance> createBSTR_CAST_CStateMachines(SimpleNode node, FSMMachine fsm) {

		String xpath = ".//CastExpression";

		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
		ASTTranslationUnit u =(ASTTranslationUnit)node.getFirstParentOfType(ASTTranslationUnit.class);
		evaluationResults = StateMachineUtils.getEvaluationResults(u, xpath);
		Iterator itr = evaluationResults.iterator();
		while(itr.hasNext()) {
			AbstractExpression CastExpression = (AbstractExpression)itr.next();	
			CType type1 = null;
			CType type2 = null;
			if(CastExpression.jjtGetNumChildren()>0&&CastExpression.jjtGetChild(1) instanceof ASTUnaryExpression) {   	
				ASTTypeName typeName =(ASTTypeName)CastExpression.jjtGetChild(0);
				ASTUnaryExpression unaryExp =(ASTUnaryExpression)CastExpression.jjtGetChild(1);
				
				type1 = typeName.getType();
				type2 =  unaryExp.getType();
				if(type1==null || type2==null)
					continue;
				if("BSTR".equals(type1.getName()) && "pointer".equals(type2.getName())) { 
					addFSM(list, CastExpression, fsm);
					ls.add(CastExpression);
				}

			}	
		}	
		return list;
	}


	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);

		if(ls.contains(node))
		{
			return;
		}

		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
			fsminstance.setDesp("Does not allow C - type data into BSTR data.");
		} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
			fsminstance.setDesp("第"+node.getBeginLine()+"行：不允许C类型数据转换为BSTR型数据");
		}	
		list.add(fsminstance);
	}
}
