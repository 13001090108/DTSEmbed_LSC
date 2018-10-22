package softtest.rules.gcc.question;

import java.util.*;

import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.*;
import softtest.symboltable.c.NameOccurrence.OccurrenceType;
import softtest.symboltable.c.Type.CType_BaseType;
import softtest.fsm.c.*;

/*
 * @author liuli 
 */
public class ANUStateMachine {
	public static List<FSMMachineInstance> createAssignNoUseStateMachines(SimpleNode node, FSMMachine fsm){
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();

		String xpath = ".//AssignmentExpression[./AssignmentOperator[@Operators='= ' or @Operators='='] ]/UnaryExpression/PostfixExpression[count(*)=1]/PrimaryExpression|"
			+ ".//Declaration[./DeclarationSpecifiers[./TypeSpecifier]]/InitDeclaratorList/InitDeclarator//Declarator/DirectDeclarator|"
			+ ".//Declaration[./DeclarationSpecifiers[./DeclarationSpecifiers[./TypeSpecifier]]]/InitDeclaratorList/InitDeclarator[./Initializer]//Declarator/DirectDeclarator ";
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		Iterator<SimpleNode> itr = evaluationResults.iterator();
			while(itr.hasNext()) {
			SimpleNode snode = itr.next();
			ASTPrimaryExpression primaryNode=null;
			VariableNameDeclaration variable=null;
			ASTDirectDeclarator qualifiedID=null;
			//变量声明时初始化和变量赋值分别处理
			if(snode instanceof ASTDirectDeclarator)
				{
				qualifiedID = (ASTDirectDeclarator) snode;
				variable = qualifiedID.getVariableNameDeclaration();
				}
			else {
				primaryNode = (ASTPrimaryExpression)snode;
				variable = primaryNode.getVariableDecl();
			}
			//end
			if(variable == null || variable.getScope() == null) {
				continue;
			}
			//step1: 变量为基本类型,过滤掉非基本的数据类型
			if(variable.getType() == null ||!(variable.getType() instanceof CType_BaseType)) {
				continue;
			}
			if(checkSpecialUse(snode)) {
				continue;
			}
			//step2:变量为局部变量
			if(!(variable.getScope() instanceof ClassScope) && !(variable.getScope() instanceof SourceFileScope)){	
				String str="static";
				String xpathstatic=".//Declaration[./DeclarationSpecifiers[./StorageClassSpecifier[@Image='"+str+"']]]/InitDeclaratorList/InitDeclarator//Declarator/DirectDeclarator[@Image='"+variable.getImage()+"']";
				List<SimpleNode> evaluationResultstatic = StateMachineUtils.getEvaluationResults(node, xpathstatic);
				//static类型的单独处理，因为static类型的变量即使最后一次赋值后未使用可能下次调用此函数时会使用
				if(!(evaluationResultstatic==null||evaluationResultstatic.size()==0)) {
					if(checkAssignNoUse(snode, variable,1)) {
						FSMMachineInstance fsmInstance = fsm.creatInstance();
						fsmInstance.setRelatedVariable(variable);
						fsmInstance.setRelatedASTNode(snode);
						addFSMDescription(fsmInstance);
						list.add(fsmInstance);
						}
				}//end
				else{
					if(checkAssignNoUse(snode, variable,0)) {
						FSMMachineInstance fsmInstance = fsm.creatInstance();
						fsmInstance.setRelatedVariable(variable);
						fsmInstance.setRelatedASTNode(snode);
						addFSMDescription(fsmInstance);
						list.add(fsmInstance);
					}
				}
			}
		}
		return list;
	}

	/**检测当前赋值变量没有在函数中被使用过*/
	public static boolean checkAssignNoUse(SimpleNode node, VariableNameDeclaration variable,int flag) {
		Scope scope = variable.getScope();
		Map<VariableNameDeclaration, ArrayList<NameOccurrence>> varOccs = scope.getVariableDeclarations();
		List<NameOccurrence> occs = varOccs.get(variable);
		if(occs.size() == 0 && Search.searchNames(variable.getImage(), varOccs) != null){
			NameOccurrence occ=new NameOccurrence(variable,node,node.getImage());
			occs.add(occ);
    	}
		List<NameOccurrence> list1 = new LinkedList<NameOccurrence>();//定义取消链
		List<NameOccurrence> list2 = new LinkedList<NameOccurrence>();//定义使用链
		//对于static类型的变量只要有一次使用出现就认为是使用过
		if(flag==1)
		{
			if(occs.size()>1)return false;
			else return true;
		}
		//对于非static类型的变量，检查是否每次赋值后都有使用
		for(NameOccurrence occ : occs) {
			if(occ.getLocation() == node) {
							list1 = occ.getDef_undef();
							list2 = occ.getDef_use();
							if((list1==null||list1.size()==0)&&(list2==null||list2.size()==0))
							{
								ASTIterationStatement iterationExpression=(ASTIterationStatement) node.getFirstParentOfType(ASTIterationStatement.class);
								if(iterationExpression==null){
									return true;
								}
								List<NameOccurrence> occAgainList = varOccs.get(variable);
								for(NameOccurrence occAgain : occAgainList){
									SimpleNode checkNode=occAgain.getLocation();
									if(checkNode.equals(node)){
										continue;
									}
									ASTIterationStatement iterationExpressionAgian=(ASTIterationStatement) checkNode.getFirstParentOfType(ASTIterationStatement.class);
									if(iterationExpressionAgian==null || !(iterationExpressionAgian.equals(iterationExpression))){
										continue;
									}
									if(occAgain.checkOccurrenceType().name().equals("USE")){
										return false;
									}
								}
							}else{
								return false;
							}
							break;
			}
		}
		return true;
	}
	
	private static boolean isUsedType(SimpleNode checkNode, VariableNameDeclaration variable) {
		Map<VariableNameDeclaration, ArrayList<NameOccurrence>> varOccs = variable.getScope().getVariableDeclarations();
    	List<NameOccurrence> occs = varOccs.get(variable);
    	for(NameOccurrence occ : occs) {
    		if(occ.getLocation() != checkNode)
    			continue;
    		if(occ.getOccurrenceType() != NameOccurrence.OccurrenceType.DEF) 
    			return true;
    	}
		return false;
	}

	/**
	 * 特殊情况单独提取处理 1. i = j = k = 0; if(!(i=get())){} 2. if((i = get())!=0){}
	 * if((i = get())==0){} if((i = get())>0){}
	 */
	private static boolean checkSpecialUse(SimpleNode node) {
		if(node instanceof ASTDirectDeclarator) return false;
		else
		{
		ASTAssignmentExpression assignment = (ASTAssignmentExpression) node.getFirstParentOfType(ASTAssignmentExpression.class);
		// i = j = k = 0; if(!(i=get())){}
		if (assignment.jjtGetParent() instanceof ASTAssignmentExpression) {
			return true;
		}
		// if((i = get())==0){} if((i = get())!=0){}
		SimpleNode equal = (SimpleNode) assignment.getFirstParentOfType(ASTEqualityExpression.class);
		if (equal != null) {
			return true;
		}
		// if((i = get())>0){}
		SimpleNode relation = (SimpleNode) assignment.getFirstParentOfType(ASTRelationalExpression.class);
		if (relation != null) {
			return true;
		}
		else
			return false;
		}
	}
	
	/**
	 * add FSMInstance description
	 */
	private static void addFSMDescription(FSMMachineInstance fsmInstance) {
		VariableNameDeclaration varDecl = fsmInstance.getRelatedVariable();
		if (varDecl.getNode() != null) {
			if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsmInstance.setDesp("The variable \"" + varDecl.getImage() + "\" which defines in line " + varDecl.getNode().getBeginLine()
						+ " is assigned in this line, but never used. This assignment belongs to useless and ill code.");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE) {
				fsmInstance.setDesp("在第 " + varDecl.getNode().getBeginLine()
						+ " 行定义的变量 \"" + varDecl.getImage() + "\" 在"+fsmInstance.getRelatedASTNode().getBeginLine()+"行被赋值，但从没有被使用过。\r该赋值属于无用赋值，不良代码。");
			}
		} else {
			if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsmInstance.setDesp("The variable \"" + varDecl.getImage()
						+ "\" is assigned in this line, but never used. This assignment belongs to useless and ill code. ");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE) {
				fsmInstance.setDesp("变量 \"" + varDecl.getImage() + "\" 在"+fsmInstance.getRelatedASTNode().getBeginLine()+"行被赋值，但从没有被使用过。\r该赋值属于无用赋值，不良代码。");
			}
		}
	}
}
