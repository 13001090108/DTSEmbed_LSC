package softtest.rules.c.fault;

import java.util.*;


import softtest.ast.c.*;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.*;
import softtest.fsm.c.*;

/** 
 * @authored by DongNa
 */

public class DNUStateMachine {
	
	public static List<FSMMachineInstance> createEDNUStateMachines(SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
	    String xpath = "";
	    Hashtable<VariableNameDeclaration, FSMMachineInstance> vfTable = new Hashtable<VariableNameDeclaration, FSMMachineInstance>();
	    List<SimpleNode> evaluationResults = null;
	   // 查询函数中所有形式参数和声明的局部变量(包含声明时初始化的变量)并为其创建状态机实例
	    //由于很多函数都只有一两句返回，很多情况都不使用形参，此模式修改下，忽略形参的问题
	    xpath = ".//ParameterList//ParameterDeclaration//Declarator/DirectDeclarator|"
	    	+".//Declaration[./DeclarationSpecifiers[./TypeSpecifier]]/InitDeclaratorList/InitDeclarator//Declarator/DirectDeclarator ";
	    evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
	   Iterator<SimpleNode> itr = evaluationResults.iterator();
	   while (itr.hasNext()) {
			ASTDirectDeclarator qualifiedID = (ASTDirectDeclarator) itr.next();
			//chh  忽略函数声明，本模式仅针对变量
			if(qualifiedID.isFunctionName())
			{
				continue;
			}
			VariableNameDeclaration variable = qualifiedID.getVariableNameDeclaration();
			
			if(variable==null){
				continue;
			}
//			if(variable != null && checkAdressType(variable)){//过滤掉&引用类型的变量
//				continue;
//			}
			if (variable != null 
					&& !vfTable.containsKey(variable)
						&& variable.getScope()!=null 
							&& !(variable.getScope() instanceof ClassScope)
								&& !(variable.getScope() instanceof SourceFileScope)) {
				FSMMachineInstance fsmInstance = fsm.creatInstance();
				fsmInstance.setRelatedVariable(variable);
				fsmInstance.setRelatedASTNode(qualifiedID);
				vfTable.put(variable, fsmInstance);
			}
	   }

		for (Enumeration<FSMMachineInstance> enm = vfTable.elements(); enm
				.hasMoreElements();) {
			list.add(enm.nextElement());
		}
		return list;
	}
	
	/**检测当前定义的变量没有被使用过*/
	public static boolean checkNoOccurence(List<SimpleNode> nodes,FSMMachineInstance fsmInst){
		boolean found = false;
		Iterator<SimpleNode> simpleNodeItr = nodes.iterator();
		
		while(simpleNodeItr.hasNext()){
			Object obj = simpleNodeItr.next();
			if(obj instanceof ASTDirectDeclarator)continue;
			if(obj instanceof ASTPrimaryExpression){
				ASTPrimaryExpression idExpression = (ASTPrimaryExpression)obj;
				if(idExpression.isMethod())
					continue;
				if(idExpression.getVariableNameDeclaration()!= null && idExpression.getVariableNameDeclaration() == fsmInst.getRelatedVariable() ){
					//SimpleNode b=fsmInst.getRelatedASTNode();//fsmInst.getRelatedASTNode()是定义的变量，idExpression是使用
					found = true;
					break;
				}
			}
			
		}
//		if(!found){
//			SimpleNode funcDef =(SimpleNode) fsmInst.getRelatedASTNode().getFirstParentOfType(ASTFunctionDefinition.class);
//			if(funcDef != null){
//				Node com_statement = funcDef.getFirstChildOfType(ASTCompoundStatement.class);
//				if(com_statement != null && com_statement.jjtGetNumChildren()==0)
//					found = true;
//				}
//			}
			
		if(!found)
			addFSMDescription(fsmInst);
		return !found;
    }
	
//	/**检测当前变量是否为&类型*/	 
//	public static boolean checkAdressType(VariableNameDeclaration var){
//		//System.out.println(var.toString());
//		CType varType = var.getType();
//		if(varType instanceof CType_Address)
//			return true;
//		else return false;
//	}
	
	private static void addFSMDescription(FSMMachineInstance fsmInstance) {
		VariableNameDeclaration varDecl = fsmInstance.getRelatedVariable();
		//SimpleNode node = fsmInstance.getRelatedASTNode();
		fsmInstance.setDesp("变量定义未使用: 变量 \""+varDecl.getImage()+"\"定义后未被使用，属于不良代码，对软件系统的性能有不良影响");
		
		}
	}

