package softtest.rules.gcc.rule;

import java.util.*;

import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.fsmanalysis.c.AnalysisElement;
import softtest.interpro.c.InterCallGraph;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.MethodNode;
import softtest.pretreatment.Pretreatment;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.*;



/** 
 * @author 
 * Static Function No Use
 * static类型的过程在所在文件中必须被调用(过程调用类)
 */

public class SFNUStateMachine {	
	//找到static类型的函数
	private static String xpath = ".//FunctionDeclaration [./DeclarationSpecifiers/StorageClassSpecifier[@Image='static']] | .//FunctionDefinition [./DeclarationSpecifiers/StorageClassSpecifier[@Image='static']]";
	//找到那些method属性为false的节点
	private static String xpath1 = ".//Statement//Expression[@Method='false'][@DescendantDepth='4'] | .//Declaration/InitDeclaratorList//DirectDeclarator[@Method='false']";
	//找到static数组，如zx_SFNU_3.cpp
	//private static String xpath2 = "//external_declaration/declaration[./declaration_specifiers/type_modifiers/storage_class_specifier[@Image='static']]/init_declarator_list/init_declarator/initializer/initializer//primary_expression/id_expression";
	private static String xpath2 = ".//ExternalDeclaration/Declaration/InitDeclaratorList/InitDeclarator/Initializer/InitializerList/Initializer//PostfixExpression/PrimaryExpression";
	
	private static List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
	private static List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
	private static Set<MethodNode> callees = new HashSet<MethodNode>();
	
	public static List<FSMMachineInstance> createSFNUMachines(SimpleNode node, FSMMachine fsm){	
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);	
		
		if(evaluationResults.size()==0) //如果该文件无static方法，直接返回null
			return null;
		
		//如果static函数定义在头文件中，应该剔除掉
		Iterator<SimpleNode> itr = evaluationResults.iterator();
		while(itr.hasNext()) {
			SimpleNode snode = itr.next();
			String fileName = snode.getFileName();
			//如果文件名是.hxx说明是头文件
			if(fileName != null && fileName.matches(InterContext.INCFILE_POSTFIX)) {
				itr.remove();
			}
		}
		
		/**找到该文件调用的所有的callees*/
		Set<MethodNameDeclaration> methods = new HashSet<MethodNameDeclaration>();
		String allMethodXpath = ".//function_definition | .//ctor_definition";
		List<SimpleNode> allMethodNode = StateMachineUtils.getEvaluationResults(node, allMethodXpath);
		itr = allMethodNode.iterator();
		while(itr.hasNext()) {
			SimpleNode snode = itr.next();
			MethodNameDeclaration methodDecl = StateMachineUtils.getMethodDefinition(snode);
			methods.add(methodDecl);
		}
		
		for(MethodNameDeclaration methodDecl : methods) 
		{	
			//如果当前的methodDecl仅仅是声明，没有定义，getMethod()返回为空
			if(/*methodDecl.isDeclOnly() ||*/ methodDecl.getMethod()==null)
				continue;
			MethodNode methodNode = InterCallGraph.getInstance().findMethodNode(methodDecl.getFileName(), methodDecl.getMethod());
			Set<MethodNode> callee  = methodNode.getCalls();
			callee.remove(methodNode); //函数调用自身的不加入
			if(callee!=null && callee.size()>0) {
				AnalysisElement element = methodNode.getElement();	
				for(MethodNode method: callee) {
					if(method.getElement()==element) 
						callees.add(method); 
				}
			}
		}
		
		/**除去对static函数的直接引用，如static void func();使用如下f(func)及f(func,...);除去此种使用*/
		List<SimpleNode> funcList = StateMachineUtils.getEvaluationResults(node, xpath1);
		for(SimpleNode snode : funcList) {
			if(snode.getVariableNameDeclaration() == null) {
				String methodName = snode.getImage();
				itr = evaluationResults.iterator();
				while(itr.hasNext()) {
					SimpleNode staticFunc = (SimpleNode) itr.next();
					MethodNameDeclaration methodDecl = StateMachineUtils.getMethodDefinition(staticFunc);
					if(methodDecl==null || methodDecl.getImage()==null)
						continue;
					if(methodName.equals(methodDecl.getImage())) {
						itr.remove();
					}
				}
			}
		}
		
		/**除去zx_SFNU_3.cpp这类问题*/
		List<SimpleNode> initlist = StateMachineUtils.getEvaluationResults(node, xpath2);
		if(initlist != null) {
			for(SimpleNode snode: initlist) {
				if(snode.getVariableNameDeclaration() == null) {
					String snodeName = snode.getImage();
					itr = evaluationResults.iterator();
					while(itr.hasNext()) {
						SimpleNode staticFunc = (SimpleNode) itr.next();
						MethodNameDeclaration methodDecl = StateMachineUtils.getMethodDefinition(staticFunc);
						if(methodDecl==null || methodDecl.getImage()==null)
							continue;
						if(snodeName.equals(methodDecl.getImage())) {
							itr.remove();
						}
					}
				}
			}
		}
		
		itr = evaluationResults.iterator();
		while(itr.hasNext()) {
			SimpleNode snode = itr.next();
			MethodNameDeclaration methodDecl = StateMachineUtils.getMethodDefinition(snode);
			if(methodDecl==null ||methodDecl.getImage()==null || methodDecl.getMethod()==null)
				continue;
			MethodNode curMethod = InterCallGraph.getInstance().findMethodNode(methodDecl.getFileName(), methodDecl.getMethod());
			if(callees.contains(curMethod)) {
				itr.remove();
			}
		}
		
		itr = evaluationResults.iterator();
		while(itr.hasNext()) {
			SimpleNode snode = itr.next();
			MethodNameDeclaration methodDecl = StateMachineUtils.getMethodDefinition(snode);
			if(methodDecl==null || methodDecl.getImage()==null || methodDecl.getMethod()==null) {
				continue;
			}
			if(methodDecl.getScope() != null && methodDecl.getScope() instanceof ClassScope) {
				continue;
			}
			addFSMDescription(snode,fsm);
		}
	    return list;
	}	

	private static void addFSMDescription(SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp("Static Function No Use.A static type function, whose scope is the file. If it is not called in this file, you should delete it. ");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("static类型的函数在所在文件中必须被调用。\r\n一个static类型的函数，它的作用域为它所在的文件。若它在所在文件中没被调用，就应该把它删掉。");
			}	
		
		list.add(fsminstance);
	}
}
