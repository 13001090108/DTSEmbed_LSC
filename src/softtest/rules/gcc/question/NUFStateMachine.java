package softtest.rules.gcc.question;

import java.util.Iterator;
//import java.util.HashMap;
//import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.ASTDeclarator;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.interpro.c.InterCallGraph;
//import softtest.interpro.c.Method;
import softtest.interpro.c.MethodNode;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.NameDeclaration;
import softtest.symboltable.c.Scope;
import softtest.symboltable.c.Search;

/** 
 * @author ssj
 * NUF(NoUsedFunction)
 */
public class NUFStateMachine {
	
	public static List<FSMMachineInstance> createNUFStateMachines(SimpleNode node, FSMMachine fsm){
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		String xPath = ".//FunctionDefinition | .//NestedFunctionDefinition";
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);
		Iterator itr = evaluationResults.iterator();
		while(itr.hasNext()){
			SimpleNode snode = (SimpleNode)itr.next();
			String interruptXpath = ".//Interrupt";
			List<SimpleNode> results = StateMachineUtils.getEvaluationResults(snode, interruptXpath);
			if(!(results.isEmpty())){
				continue;
			}
			ASTDeclarator declarator = null;
			if((snode.jjtGetNumChildren() > 1) && (snode.jjtGetChild(1) instanceof ASTDeclarator)){
				declarator = (ASTDeclarator)snode.jjtGetChild(1);
			}
			else{
				continue;
			}
			if(declarator.getImage().equals("main")){
				continue;
			}else{
				String image = snode.getImage();
				Scope scope = snode.getScope();
				NameDeclaration decl=Search.searchInMethodUpward(image, scope);
				MethodNameDeclaration mnd = (MethodNameDeclaration)decl;
				if(mnd.isLib()){
					continue;
				}
				InterCallGraph interCallGraph = InterCallGraph.getInstance();
//				HashMap<Method, MethodNode> interMethodTable = new LinkedHashMap<Method, MethodNode>();
//				interMethodTable = interCallGraph.getCallRelationTable();
//				Method method = mnd.getMethod();
//				MethodNode mtNode = interMethodTable.get(method);
				List<MethodNode> MethodNodeTable = interCallGraph.getMethodTopoOrder();
				boolean flag = false;
				for(MethodNode methodNode : MethodNodeTable){
					List<MethodNode> callSet = methodNode.getOrderCalls();
					if(callSet.size() == 0){
						continue;
					}else{
						for(MethodNode mthNode : callSet){
							if(mthNode.getMethod() != null){
//								if(mtNode.getMethod().getName().equals(mthNode.getMethod().getName())){
								if(image.equals(mthNode.getMethod().getName())){
									flag = true;
									break;
								}
							}
						}
						if(flag){
							break;
						}
					}
				}
				if(!flag){
					addFSM(snode,fsm,list);
				}
			}
		}
		return list;
	}
	/**
	 * 将没有使用过的函数加入到list中
	 */
	private static void addFSM(SimpleNode node, FSMMachine fsm, List<FSMMachineInstance> list) {	
		for(FSMMachineInstance instance : list) {
			if(instance.getRelatedASTNode() == node) 
				return ;
		}
		FSMMachineInstance fsminstance = fsm.creatInstance();			
		fsminstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH)
			fsminstance.setDesp("The function is never used. This function belongs to useless code.");
		else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
			fsminstance.setDesp("在"+node.getBeginLine()+"行出现了从未被使用过函数。\r\n该函数不会被调用，属于冗余代码，却增加了可执行文件的长度。");	

		list.add(fsminstance);
	}
}
