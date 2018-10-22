package softtest.rules.gcc.question;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.ASTDeclarator;
import softtest.ast.c.ASTInitDeclarator;
import softtest.ast.c.ASTInitializer;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.AbstractExpression;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.Type.CType;

/*
 * author:Wangjing
 * 模式：BSTR.IA.INIT：BSTR变量初始化(Question:BSTR)
 * 
 * */
public class BSTR_IA_INITStateMachine {
	
	public static List<FSMMachineInstance> createBSTR_IA_INITMachines(SimpleNode node, FSMMachine fsm) {
		
		String xpath = ".//InitDeclarator";
		
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
		
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		Iterator itr = evaluationResults.iterator();
		
		while(itr.hasNext()) {
			
			ASTInitDeclarator astid = (ASTInitDeclarator)itr.next();
			
			int childNum = astid.jjtGetNumChildren();
			
			if (childNum == 2) {
				
				ASTDeclarator declarator = (ASTDeclarator)astid.jjtGetChild(0);
				
				ASTInitializer initializer = (ASTInitializer)astid.jjtGetChild(1);
				
				ASTPrimaryExpression astpe = (ASTPrimaryExpression)initializer.getFirstChildOfType(ASTPrimaryExpression.class); 
				
				String value = astpe.getImage();
				
				CType type1 = declarator.getType();
				CType type2 = astpe.getType();
				if(type1 == null || type2==null)
					continue;
			
				String name1 = type1.getName();
				String name2 = type2.getName();
				
				if ("BSTR".equals(name1) && (
						(!"CcomBSTR".equals(name2)) && 
						(!"BSTR".equals(name2)) &&
						(!"bstr_t".equals(name2)) &&
						(!("".equals(value)&&("pointer".equals(name2))))						
						)) {
					addFSM(list, astid, fsm);
				}
				
			}
		}
		
		return list;
		
	}
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		
		FSMMachineInstance fsminstance = fsm.creatInstance();
		
		fsminstance.setRelatedASTNode(node);
		
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
			fsminstance.setDesp("BSTR variable may not have been initialized to NULL or a BSTR CcomBSTR , bstr_t value.");
		} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
			fsminstance.setDesp("第"+node.getBeginLine()+"行：BSTR变量可能未被初始化为NULL或BSTR、CcomBSTR、bstr_t型值。");
		}	
		list.add(fsminstance);
	}

}
