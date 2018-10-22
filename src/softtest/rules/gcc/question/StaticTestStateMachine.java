package softtest.rules.gcc.question;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.ASTDeclaration;
import softtest.ast.c.ASTDirectDeclarator;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.Node;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;


/*
 * @author yx
 * 如果一个文件级的静态变量仅在一个函数中被使用/引用，就应该只在该函数内部包含此变量 
 */
public class StaticTestStateMachine {

	public static List<FSMMachineInstance> createStaticTestStateMachines(SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = null;
		
		
		ASTTranslationUnit  translationUnitNode = (ASTTranslationUnit)node.getFirstParentOfType(ASTTranslationUnit.class);
		if(translationUnitNode==null)
		{
			return list;
		}
		
		String xpath =".//StorageClassSpecifier";
		evaluationResults = StateMachineUtils.getEvaluationResults(translationUnitNode, xpath);
		Iterator<SimpleNode> itr = evaluationResults.iterator();
	    List<SimpleNode> staticList  =new ArrayList<SimpleNode>(); 
	    String xpath2=".//FunctionDefinition";
		List<SimpleNode> evaluationResults2 = StateMachineUtils.getEvaluationResults(translationUnitNode, xpath2);
		int i;
		while(itr.hasNext()) 
		{
			i=0;
			SimpleNode sNode = (SimpleNode)itr.next();
			ASTDirectDeclarator de=(ASTDirectDeclarator)((SimpleNode)(sNode.getFirstParentOfType(ASTDeclaration.class))).getFirstChildOfType(ASTDirectDeclarator.class);
		    Iterator<SimpleNode> it = evaluationResults2.iterator();
		    while(it.hasNext())
		    {
		    	SimpleNode s = (SimpleNode)it.next();
		    	//s.getFirstParentOfType(ASTDeclaration.classe).;
		    	List<Node> child = s.findChildrenOfType(ASTPrimaryExpression.class);
		    	Iterator<Node> itt = child.iterator();
		    	while(itt.hasNext())
		    	{
		    		if(((SimpleNode)itt.next()).getImage().equals(de.getImage()))
		    		{		
		    			  i++;
		    		      break;
		    		}
		    	}
		    	
		    }
		            if(i==1)
		    	addFSM(list, sNode, fsm);
			
	    }  
		
		
		return list;
	}
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsmInstance = fsm.creatInstance();
		fsmInstance.setRelatedASTNode(node);
		
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) 		
			fsmInstance.setDesp("Warning: Line" + fsmInstance.getRelatedASTNode().getBeginLine()+" TYPEDEF usage error: Empty typedef");
		else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
			fsmInstance.setDesp("警告：第" + fsmInstance.getRelatedASTNode().getBeginLine()+" 行静态变量仅在一个函数中被使用/引用");
		
		list.add(fsmInstance);
	}
}