package softtest.rules.gcc.question;
import java.util.*;

import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.interpro.c.InterContext;
import softtest.rules.c.StateMachineUtils;


/*
 * @author liruitong
 * 空typedef使用错误，eg: typedef int; 
 */
public class EMPTYStateMachine {

	public static List<FSMMachineInstance> createEMPTYStateMachines(SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = null;
		
		
		ASTTranslationUnit  translationUnitNode = (ASTTranslationUnit)node.getFirstParentOfType(ASTTranslationUnit.class);
		if(translationUnitNode==null)
		{
			return list;
		}
		
		String xpath =".//DeclarationSpecifiers/StorageClassSpecifier[@Image='typedef']";
		evaluationResults = StateMachineUtils.getEvaluationResults(translationUnitNode, xpath);
		Iterator<SimpleNode> itr = evaluationResults.iterator();
	
		while(itr.hasNext()) {
			SimpleNode sNode = (SimpleNode)itr.next();
			String filename = sNode.getFileName();
			if(filename==null || filename.matches(InterContext.INCFILE_POSTFIX))
				continue;
			if (sNode.jjtGetParent().jjtGetParent().jjtGetNumChildren()<2)
			{
				addFSM(list, sNode, fsm);
			}
		}
		 return list;
	}
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsmInstance = fsm.creatInstance();
		fsmInstance.setRelatedASTNode(node);
		
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) 		
			fsmInstance.setDesp("Warning: Line" + fsmInstance.getRelatedASTNode().getBeginLine()+" TYPEDEF usage error: Empty typedef");
		else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
			fsmInstance.setDesp("警告：第" + fsmInstance.getRelatedASTNode().getBeginLine()+" 行TYPEDEF使用错误：空typedef内容");
		
		list.add(fsmInstance);
	}
}
