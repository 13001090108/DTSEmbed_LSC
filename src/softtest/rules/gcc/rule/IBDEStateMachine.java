package softtest.rules.gcc.rule;

import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.*;
import softtest.symboltable.c.Type.CType;
import softtest.ast.c.SimpleNode;

/**
 * @author LiuChang
 * InnerBlockRedefineVariable
 * 内部块中重定义已有的变量名 
 **/

public class IBDEStateMachine {

	public static List<FSMMachineInstance> createIBDEStateMachines(SimpleNode node, FSMMachine fsm){
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = null;
		Hashtable<String, Scope> scopeTable = new Hashtable<String, Scope>();
		
		String xPath = ".//CompoundStatement//Declaration[./DeclarationSpecifiers]/InitDeclaratorList[@Image !='(']/InitDeclarator/Declarator//DirectDeclarator";
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);
		Iterator itr = evaluationResults.iterator();
		
		
		
		while(itr.hasNext()){
			ASTDirectDeclarator id = (ASTDirectDeclarator)itr.next();
			VariableNameDeclaration var =id.getVariableNameDeclaration();
			if(var == null)
				continue;
			if(var.isParam())
				continue;
			Scope scope = id.getScope();
			NameDeclaration variable = id.getDecl();
			if(variable == null)
				continue;
			String name = variable.getImage();
			if(!scopeTable.containsKey(name))
				scopeTable.put(name, scope);
			else{
				if(scope.isSelfOrAncestor(scopeTable.get(name)))
					addFSM(list,id,fsm);
				else scopeTable.put(name, scope);
			}
		}
		return list;
		
  }

	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp("nnerBlockRedefineVariable ： Redefinition in inner block is permitted but is a bad habit of programing.So it's better to use another name.");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("内部块中重定义已有的变量名: 块结构允许在内部块中重定义已有的变量名："+node.getImage().toString()+"，但这是不好的编程习惯，且容易出现编程失误，因此禁止在内部块中重定义已有的变量名。");
			}	
		
		list.add(fsminstance);
	}
}


