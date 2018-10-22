package softtest.rules.keilc.fault;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import softtest.ast.c.*;
import softtest.fsm.c.*;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.*;
import softtest.symboltable.c.Type.CType;
import softtest.symboltable.c.Type.CType_BaseType;



/**
 * @author zx
 * Double Assigned Not Used [变量赋值后，未使用前再次赋值]
 * zys:多次赋值未使用
 * 经检测存在误报，具体见回归测试中的06测试用例,请修改！		zys		2010.3.29
 * */
public class DANUStateMachine {
	
	/**
	 * 为函数中那些显示赋值的变量创建状态机（例如 d = 10）
	 * a[1]=1, a.b=1, a->b = 1不处理
	 * */
	public static List<FSMMachineInstance> createDANUStateMachines(SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		//chh  对在声明时初始化的变量也创建状态机
		String xpath = ".//AssignmentExpression[./AssignmentOperator[@Operators='= ' or @Operators='='] ]/UnaryExpression/PostfixExpression[count(*)=1]/PrimaryExpression|"
			+ ".//Declaration[./DeclarationSpecifiers[./TypeSpecifier]]/InitDeclaratorList/InitDeclarator[./Initializer]//Declarator/DirectDeclarator ";
			
		
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		Iterator<SimpleNode> itr = evaluationResults.iterator();
			while(itr.hasNext()) {
			SimpleNode snode = itr.next();
			ASTPrimaryExpression primaryNode;
			VariableNameDeclaration variable;
			ASTDirectDeclarator qualifiedID;
			// chh 变量声明时初始化和变量赋值分别处理
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
				//得到当前赋值语句的最外层循环节点
				SimpleNode itrNode = getIteration(snode);
				//step2.1 如果当前赋值语句变量被重新定义，而且无使用出现，报错
				if(checkAssignedAgain(snode, variable)) {
					FSMMachineInstance fsmInstance = fsm.creatInstance();
					fsmInstance.setRelatedVariable(variable);
					fsmInstance.setRelatedASTNode(snode);
					addFSMDescription(fsmInstance);
					list.add(fsmInstance);
					continue;
				}
				//step2.2 如果当前赋值语句是存在循环中,如果该循环中出现了该变量的使用，视当前赋值变量被使用
				else if(itrNode != null) {
					int beginLine = itrNode.getBeginLine();
					int endLine = itrNode.getEndLine();
					if(!checkHasUsed(variable, beginLine, endLine)) {
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
	
	/**
	 * 在于循环语句（for、while、do-while）中的是否存在对变量的使用出现
	 * */
	private static boolean checkHasUsed(VariableNameDeclaration variable, int beginLine, int endLine) {
		Scope scope = variable.getScope();
		Map<VariableNameDeclaration, ArrayList<NameOccurrence>> varOccs = scope.getVariableDeclarations();
    	List<NameOccurrence> occs = varOccs.get(variable);
    	for(NameOccurrence occ : occs) {
    		//此次出现非定义出现
    		if(occ.checkOccurrenceType() != NameOccurrence.OccurrenceType.DEF) {
    			SimpleNode snode = occ.getLocation();
        		int curLine = snode.getBeginLine();
        		if(curLine >= beginLine && curLine <= endLine) {
        			return true;
        		}
    		}
    	}
		return false;
	}

	/**忽略所有存在于循环语句（for、while、do-while）中的赋值语句，因为会产生很多的误报*/
	private static SimpleNode getIteration(SimpleNode node) {
		SimpleNode result = null;
		SimpleNode ancestor = (SimpleNode) node.jjtGetParent();
		while(!(ancestor instanceof ASTTranslationUnit)) {
			if(ancestor instanceof ASTIterationStatement) {
				result = ancestor;
			}
			ancestor = (SimpleNode) ancestor.jjtGetParent();
		}
		return result;
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
	
	/**检测当前赋值变量没被使用但再次赋值，返回true*/
	private static boolean checkAssignedAgain(SimpleNode node, VariableNameDeclaration variable) {
		Scope scope = variable.getScope();
		Map<VariableNameDeclaration, ArrayList<NameOccurrence>> varOccs = scope.getVariableDeclarations();
    	List<NameOccurrence> occs = varOccs.get(variable);
		List<NameOccurrence> list1 = new LinkedList<NameOccurrence>();//定义取消链
		List<NameOccurrence> list2 = new LinkedList<NameOccurrence>();//定义使用链
		if(occs==null)
			return false;
		for(NameOccurrence occ : occs) {

			if(occ.getLocation() == node) {
							list1 = occ.getDef_undef();
							list2 = occ.getDef_use();
							if(list2==null||list2.size()==0)  
								{
								break;
								}
							
							else 
								{
								if(list2.size() >0)
									{
										if(list2.size()==list1.size()&&list1.size()>0&&list2.size()>0)
										{
											//chh  对于i=i+*;类似的先使用后赋值的语句，如果接着再对i赋值，为冗余赋值。
											if(list2.get(0).getLocation().getBeginLine()==occ.getLocation().getBeginLine()) 
												{
												
												if(list2.get(0).getLocation().getBeginColumn()-occ.getLocation().getEndColumn()<=2)
													return true;
												}
											if(list2.get(0).getLocation().getBeginLine()>list1.get(0).getLocation().getBeginLine()) 
												return true;
											//end
										}
										//chh 对于在本次定义出现 可到达的 下次使用出现之前的 定义出现 视为对当前变量的重复赋值
										if(list1.size()>0&&list2.get(0).getLocation().getBeginLine()>list1.get(0).getLocation().getBeginLine()) 
											return true;
									return false;
									}
								else {
									return true;
									}
								}
						}
					}
					if(list1.size()>0 &&(list2==null|| list2.size()==0))
					{
						return true;
					}
					else
						return false;
	}
	
	/**
	 * add FSMInstance description
	 */
	private static void addFSMDescription(FSMMachineInstance fsmInstance) {
		VariableNameDeclaration varDecl = fsmInstance.getRelatedVariable();
		if (varDecl.getNode() != null) {
			fsmInstance.setDesp("在第 " + varDecl.getNode().getBeginLine() + " 行定义的变量 \"" + varDecl.getImage() + "\" 在本行被赋值，但没被使用过又再次赋值。");
		} else {
			fsmInstance.setDesp("变量 \"" + varDecl.getImage() + "\"在本行被赋值，但从没有被使用过又再次赋值。");
		}
	}
	
}