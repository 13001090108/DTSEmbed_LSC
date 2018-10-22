package softtest.rules.gcc.rule;

import java.util.*;

import softtest.ast.c.*;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.interpro.c.InterContext;
import softtest.pretreatment.Pretreatment;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.*;
import softtest.symboltable.c.Type.*;



/** 
 * @author maojinyu
 * Function Parameter According 2
 * 函数定义与函数声明的参数、返回类型必须一致（个数、类型） (过程调用类)
 */
public class FPA2StateMachine {	
	
	private static List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
	private static List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
	private static List<SimpleNode> evaluationResults2 = new LinkedList<SimpleNode>();
	private static List<SimpleNode> evaluationResults3 = new LinkedList<SimpleNode>();
	private static List<SimpleNode> evaluationResults4 = new LinkedList<SimpleNode>();
	private static List<SimpleNode> evaluationResults5 = new LinkedList<SimpleNode>();
	private static List<SimpleNode> evaluationResults6 = new LinkedList<SimpleNode>();
	
	
	public static List<FSMMachineInstance> createFPA2Machines(SimpleNode node, FSMMachine fsm){
		
		//如果当前函数在编译库文件、头文件中,跳过
		String filename = node.getFileName();
		if(filename==null || filename.matches(InterContext.INCFILE_POSTFIX))
			return null;
		
		//找到所有的函数定义节点
		
		String xpath = ".//FunctionDefinition";	
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		
		//找到所有函数声明节点
		String xpath2 = ".//FunctionDeclaration";
		evaluationResults2 =StateMachineUtils.getEvaluationResults(node, xpath2);
		
		
		for(SimpleNode snode : evaluationResults) {	
			MethodNameDeclaration methodDef = StateMachineUtils.getMethodDefinition(snode);
			String curMethodName = methodDef.getImage();
			//比较函数定义与函数声明节点的参数、返回类型是否一致
			Iterator<SimpleNode> itr2 = evaluationResults2.iterator();
			while(itr2.hasNext()) {
				SimpleNode methodDecl = itr2.next();
				String methodName = methodDecl.getImage();
				if( methodName.equals(curMethodName)) {
				
					//如果函数定义与函数声明节点不一致
					if(!compareTwoFunc(snode, methodDecl, methodDef, fsm)) {
						itr2.remove();
						break;
					}
				}
			}
		}
	    return list;
	}	
	
	/*
	 * 比较函数定义与函数声明节点的参数、返回类型是否一致,返回不一致则返回false
	 * methodDecl 函数声明
	 * methodDef 函数定义
	 */
	private static boolean compareTwoFunc(SimpleNode snode, SimpleNode methodDecl, MethodNameDeclaration methodDef, FSMMachine fsm) {		
		
		boolean flag = true;
		
		
	
		
	
		String paramxpath = "//ParameterTypeList/ParameterList/ParameterDeclaration/DeclarationSpecifiers";	
		evaluationResults3 = StateMachineUtils.getEvaluationResults(methodDecl, paramxpath);
		evaluationResults4 = StateMachineUtils.getEvaluationResults(snode, paramxpath);
		int defNum = evaluationResults4.size();
		
		int declNum =evaluationResults3.size();
		
		
		String returnxpath = "//DeclarationSpecifiers";
		evaluationResults5 = StateMachineUtils.getEvaluationResults(methodDecl, returnxpath);
		evaluationResults6 = StateMachineUtils.getEvaluationResults(snode, returnxpath);
		

		//如果参数个数不匹配直接退出
		if(declNum!=defNum){
			
			addNumDesp(methodDecl, fsm, methodDef, declNum, defNum);
			flag = false;
		}
		
		else{
			//得到函数定义及函数声明的参数类型
			List<CType> declparams = new ArrayList<CType>();
			List<CType> defparams = new ArrayList<CType>();
						
		for(int i=0;i<evaluationResults3.size();i++){
			
			ASTDeclarationSpecifiers declparam = (ASTDeclarationSpecifiers)evaluationResults3.get(i); 
			ASTDeclarationSpecifiers defparam = (ASTDeclarationSpecifiers)evaluationResults4.get(i);
			declparams.add(declparam.getType());
			defparams.add(defparam.getType());
			
		}
		
		//比较函数定义和函数声明的参数类型
		if(declparams!=null)
			if(!(declparams.equals(defparams))){
				
				addTypeDesp(methodDecl, fsm, declparams, defparams);
				flag = false;
		}
		
		//得到函数定义和函数声明的返回类型
		if(evaluationResults5.size()>0&&evaluationResults6.size()>0){
		ASTDeclarationSpecifiers declreturn = (ASTDeclarationSpecifiers)evaluationResults5.get(0); 
		ASTDeclarationSpecifiers defreturn = (ASTDeclarationSpecifiers)evaluationResults6.get(0);
		
		CType declreturntype=declreturn.getType();
		CType defreturntype=defreturn.getType();
		
		//比较函数定义和函数声明的返回类型
		if(!(declreturntype.equals(defreturntype))){
			
			addReturnDesp(methodDecl, fsm, declreturntype, defreturntype);
			flag = false;
		
		}}
		
		
		
			}

	
		return flag;
	}


	/*
	 * 函数声明与函数定义的参数个数不匹配
	 */
	private static void addNumDesp(SimpleNode node, FSMMachine fsm, MethodNameDeclaration methodDef,int declNum, int defNum) {	
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		String defDesp = methodDef.getImage();
	
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
			fsminstance.setDesp(node.getImage() + " Function parameter number must be according.");
		} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
			fsminstance.setDesp("函数 "+defDesp+"的函数声明与函数定义的参数个数不匹配。" );
		}		
		list.add(fsminstance);
	}
	
	/*
	 * 函数声明与函数定义的参数类型不匹配
	 */
	private static void addTypeDesp(SimpleNode node, FSMMachine fsm, List<CType> declTypes, List<CType> defTypes) {	
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
			fsminstance.setDesp(node.getImage() + " Function parameter Type must be according.");
		} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
			fsminstance.setDesp("函数"+node.getImage()+"的函数声明与函数定义的参数类型不匹配。函数声明参数类型为 "+ declTypes.toString()+",而函数定义参数类型为 "+defTypes.toString());
		}	
		list.add(fsminstance);
	}
	
	/*
	 * 函数声明与函数定义的返回值类型不匹配
	 */
	private static void addReturnDesp(SimpleNode node, FSMMachine fsm, CType declType, CType defType) {	
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
			fsminstance.setDesp(node.getImage() + " Function parameter Type must be according.");
		} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
			fsminstance.setDesp("函数"+node.getImage()+"的函数声明与函数定义的返回值类型不匹配。函数声明参数类型为 "+ declType.toString()+",而函数定义参数类型为 "+defType.toString());
		}	
		list.add(fsminstance);
	}

}
