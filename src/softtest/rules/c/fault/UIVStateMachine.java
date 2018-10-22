package softtest.rules.c.fault;


import java.util.ArrayList;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import softtest.ast.c.*;
import softtest.cfg.c.VexNode;
import softtest.fsm.c.*;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.*;
import softtest.symboltable.c.Type.*;



/**
 * @author zx
 * UnInited Variable[未初始化变量]
 * */
public class UIVStateMachine {
	
	/**为每个没有初始化的非静态、非外部的局部变量创建状态机*/
	public static List<FSMMachineInstance> createUIVStateMachines(SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		Hashtable<VariableNameDeclaration, FSMMachineInstance> fsmInsTable = new Hashtable<VariableNameDeclaration, FSMMachineInstance>();
		   
		 //查找当前函数中的所有非静态、非外部类型的局部变量, 没有初始化表达式DeclarationList/
		String xpath = ".//Declaration[./DeclarationSpecifiers[not(./StorageClassSpecifier)]]/InitDeclaratorList/InitDeclarator[not(./Initializer)]/Declarator/DirectDeclarator"; 
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		/**为当前赋值后的变量创建状态机实例*/
		Iterator<SimpleNode> itr = evaluationResults.iterator();
		while(itr.hasNext()) {
			SimpleNode snode = itr.next();
			ASTDirectDeclarator primaryNode = (ASTDirectDeclarator)snode;
			VariableNameDeclaration variable = primaryNode.getVariableNameDeclaration();
			if(variable == null) {
				continue;
			}
			CType type = variable.getType();	
			//只处理基本普通类型的变量和数组类型
			if(!(type instanceof CType_BaseType || type instanceof CType_Array || type instanceof CType_Pointer)) {
				continue;
			}
			//数组类型只考虑，数组成员是简单类型的变量
	    	if (type instanceof CType_Array && !(((CType_Array)type).getOriginaltype() instanceof CType_BaseType)) {
	    		continue;
	    	}
	    	//仅为当前函数中局部变量创建状态机实例
	    	if(!(variable.getScope() instanceof LocalScope || variable.getScope() instanceof MethodScope)){
	    		continue;
	    	}
	    	if (variable.isParam()) {
	    		continue;
	    	}
	    	if(!(fsmInsTable.containsKey(variable))){
	    		FSMMachineInstance fsmInstance = fsm.creatInstance();
				fsmInstance.setRelatedVariable(variable);
				fsmInstance.setRelatedASTNode(snode);
				fsmInsTable.put(variable, fsmInstance);
				list.add(fsmInstance);
	    	}
		}
		return list;
	}
	
	/**检测控制流节点上是否包含状态机相关的变量*/
	public static boolean checkSameVariable(List<Node> nodeList, FSMMachineInstance fsmInst) {
		Iterator<Node> listItr = nodeList.iterator();
		while(listItr.hasNext()) {
			ASTDirectDeclarator checkNode = (ASTDirectDeclarator) listItr.next();
			VariableNameDeclaration variable = checkNode.getVariableNameDeclaration();
			if(variable != null && variable == fsmInst.getRelatedVariable() && checkNode == fsmInst.getRelatedASTNode()) {
				return true;
			}			
		}
		return false;
	}
	
	/**检测状态机相关变量是否被初始化*/
	public static boolean checkInial(VexNode checkedVexNode, FSMMachineInstance fsmInst) {
		
		//chh  对于**head节点暂时认为未初始化，因为getTreenode()返回整个语句块，在后面的checkUse函数中处理
		if(checkedVexNode.isBackNode()||
				checkedVexNode.getName().startsWith("for_head")||checkedVexNode.getName().startsWith("if_head")
				||checkedVexNode.getName().startsWith("while_head")||checkedVexNode.getName().startsWith("do_while_head")){//不对尾节点进行处理
			return false;
		}
		SimpleNode releatedTreeNode = checkedVexNode.getTreenode();
		if (isInit(fsmInst.getRelatedVariable(), releatedTreeNode)) {
				fsmInst.setFlag(true);
				fsmInst.setReleatedVexNode(checkedVexNode);
				return true;
		}
		return false;
	}
	
	/**
	 * 检测状态机相关变量是否被初始化
	 * 仅仅处理循环语句的尾节点while_out、for_out
	 * 假定能够进入while/for循环，并且变量在其中初始化了，出循环后，默认为该变量已初始
	 * 
	 * 如果该方法不存在，只存在上述的checkInial，因为UVF被认为是路径敏感，所以可能会认为有一条没有进while循环的路径，导致误报（路径铭感不会导致漏报的）
	 * 加该方法的目的仅仅是减少因为循环语句引起的太多误报
	 * */
	public static boolean checkArrayInial(VexNode checVexNode, FSMMachineInstance fsmInst) {
		if (!(checVexNode.getName().startsWith("for_out") || checVexNode.getName().startsWith("while_out"))) {
			return false;
		}
		SimpleNode releatedTreeNode = checVexNode.getTreenode();
		VariableNameDeclaration varDecl = fsmInst.getRelatedVariable(); 
		
		if (isInit(varDecl, releatedTreeNode)) {
			fsmInst.setFlag(true);
			fsmInst.setReleatedVexNode(checVexNode);
			return true;
		}
		return false;
	}
	

	public static boolean isInit(VariableNameDeclaration varDecl, SimpleNode node) {
		
		//step1通过系统函数初始化
		
		//step1.1: 通过函数sscanf( const char *, const char *, ...);进行初始化
		String ioInialXpath = ".//PostfixExpression[./PrimaryExpression[@Image='sscanf']]/ArgumentExpressionList/AssignmentExpression[last()]//PostfixExpression[not(./Expression)]/PrimaryExpression[count(*)=0]";
		List<SimpleNode> cinList = StateMachineUtils.getEvaluationResults(node,ioInialXpath);	
		for( SimpleNode tnode : cinList){			
			ASTPrimaryExpression checkExp = (ASTPrimaryExpression)tnode;
			if(checkExp.getVariableNameDeclaration() == null){
				continue;
			}else{
				//zx: 判断该节点可达否，不可达直接返回false
				if(checkExp.getCurrentVexNode() != null && checkExp.getCurrentVexNode().getContradict()) {
					return false;
				}
				if(checkExp.getVariableNameDeclaration() == varDecl) {
					return true;
				}
			}
		}	
		
		//step1.2 先除掉strcpy(dest,src)中第二个元素不对其进行初始化；
		//同理strncpy(dest,src)不对其第二个元素进行初始化，当变量作为第二个参数传入时，返回false
		//step1.3 同理，也应该除去strcmp(str1, str2)、strstr(str1, str2)，其中两个参数都应该初始化
		String defaultFunList[] = {"strcpy", "strncpy","memcpy", "memmove", "strcat", "strncat"};
		String cmpFuncList[] = {"strstr", "strcmp", "strncmp", "memcmp"};
		
		String ioNoInialxPath=".//PostfixExpression[./ArgumentExpressionList[count(*)=2]/AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression[@Image='" + varDecl.getImage() + "']]/PrimaryExpression";
		List<SimpleNode> funInialList = StateMachineUtils.getEvaluationResults(node, ioNoInialxPath);
		//step1.2  对于defaultFunList和cmpFuncList中的函数,变量位于特定形参的位置必须初始化过
		//chh  将对cmpFuncList类型的函数的判断与对defaultFunList类型函数的判断放到一个for循环，避免多次循环
		for (SimpleNode idexp : funInialList) {	 
			ASTPrimaryExpression func = (ASTPrimaryExpression)idexp;
			SimpleNode expList = (SimpleNode) idexp.jjtGetParent().jjtGetChild(1);
			if (expList == null) {
				continue;
			}
			
			String funcName = func.getImage();			
			for(String name : defaultFunList) {
				if(funcName.equals(name)) {
					//第二形参位置变量
					List<SimpleNode>  list = StateMachineUtils.getEvaluationResults(expList, "./AssignmentExpression[last()]/UnaryExpression/PostfixExpression/PrimaryExpression");
					SimpleNode arg1 = list.get(0);
					if(arg1.getImage().equals(varDecl.getImage())) {
						return false;
					}
				}
			}
			for(String name : cmpFuncList) {
				if(funcName.equals(name)) {
					List<SimpleNode>  list = StateMachineUtils.getEvaluationResults(expList, "./AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression");
					SimpleNode arg = list.get(0);//变量位于第一形参的位置
					if(arg.getImage().equals(varDecl.getImage())) {
						return false;
					}
					arg = list.get(1);//变量位于第二形参的位置
					if(arg.getImage().equals(varDecl.getImage())) {
						return false;
					}
				}
			}
			return true;
		}
		//step1.2_end
		
		
		// step2.1: 通过函数调用进行初始化，如果将变量取地址做参数传入函数中，则默认该变量由当前函数进行初始化
		// 形如: func(&a); scanf("%d", &a); func(&a, 1);两者语法树稍有不同，C++特定的语法造成(此处语法无区别)
		String xPath = ".//PostfixExpression[./PrimaryExpression]/ArgumentExpressionList/AssignmentExpression/UnaryExpression[./UnaryOperator[@Operators='&']]/UnaryExpression/PostfixExpression/PrimaryExpression";
		funInialList = StateMachineUtils.getEvaluationResults(node, xPath);
		for (SimpleNode idExp : funInialList) {
			ASTPrimaryExpression snode = (ASTPrimaryExpression)idExp;
			//zx: 判断该节点可达否，不可达直接返回false
			if(idExp.getCurrentVexNode()!= null && idExp.getCurrentVexNode().getContradict()) {
				//return false;
				continue;
			}
			if (snode.getVariableNameDeclaration() != null && snode.getVariableNameDeclaration() == varDecl) {
				return true;
			}
		}
		
		
		//step2.2: 通过函数调用进行初始化， 如果将变量传引用，则默认该变量由当前函数进行初始化
		//声明void func(int &i, int b);
		//当调用func(i, 0);时默认为对i进行了初始化(无传引用)
		//step2.3: int * array;或者 int array[10];时
		//func(array, b);传入时，array为指针类型，视为func函数将其初始化
		xPath=".//PostfixExpression[./ArgumentExpressionList/AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression[@Image='" + varDecl.getImage() + "']]/PrimaryExpression";
		funInialList = StateMachineUtils.getEvaluationResults(node, xPath);
		for (SimpleNode idexp : funInialList) {
			//zx: 判断该节点可达否，不可达直接返回false
			if(idexp.getCurrentVexNode()!= null && idexp.getCurrentVexNode().getContradict()) {
				//return false;
				continue;
			}
			// 变量类型为数组或者指针时，视为对其初始化
			if (varDecl.getType() instanceof CType_AbstPointer) { 
				return true;
			}
		}
		
		
		//step3.1:但是针对AST的特殊语法void f(int &)定义，当调用f(i)时，算是给i进行赋值操作
		//声明void func(int &i);传入参数的引用
		//当调用func(i);时默认为对i进行了初始化(无)
		//zx: step3.2: 但是针对AST的特殊语法void f(int *)定义，当调用f(array)时，算是给array进行赋值操作[array为数组或指针类型]
		//声明void func(int *array);
		
		
		//step4: “=”显示赋值的变量
		// 从第一判断位置转到最后，避免int i; i = i + 1;这种情况
		String assignInial = ".//AssignmentExpression[./AssignmentOperator[@Operators='= ' or @Operators='=']]";
		List<SimpleNode> assignNodeList = StateMachineUtils.getEvaluationResults(node, assignInial);
		Iterator<SimpleNode> assignItr = assignNodeList.iterator();
		while(assignItr.hasNext()){
			ASTAssignmentExpression assignNode = (ASTAssignmentExpression) assignItr.next();
			//zx: 判断该节点可达否，不可达，直接返回false
			if(assignNode.getCurrentVexNode() != null && assignNode.getCurrentVexNode().getContradict()) {
				return false;
				
			}
			//找到赋值表达式左边的那个变量
			String inialExpressionXpath = "./UnaryExpression/PostfixExpression[not(./FieldId)]/PrimaryExpression[@Image='"+ varDecl.getImage() +"'and count(*)= 0]";
			List<SimpleNode> inialExpList = StateMachineUtils.getEvaluationResults(assignNode, inialExpressionXpath);
			Iterator<SimpleNode> itr = inialExpList.iterator();
			while(itr.hasNext()){
			ASTPrimaryExpression idExp = (ASTPrimaryExpression) itr.next();
			if (idExp.getVariableNameDeclaration() != null && idExp.getVariableNameDeclaration() == varDecl) {
					//zx: 判断‘=’右边是否也出现了同一个变量，如i = i + 1;
					//小心int i; i = a.i;此类问题。故不能直接.//id_expression，会引来误报
					String sameVariableXpath = ".//UnaryExpression/PostfixExpression[not(./FieldId)]/PrimaryExpression[@Image='"+ varDecl.getImage() +"' and count(*)= 0]";
					List<SimpleNode> inialList = StateMachineUtils.getEvaluationResults((SimpleNode)assignNode.jjtGetChild(2), sameVariableXpath);
					if(inialList != null && inialList.size() > 0) {
						//chh: 判断‘=’右边是否也出现了同一个变量，如array[1] = array[0] = 0;
						//添加判断，对”array[1] = array[0] = 0;“和”array[1] = array[0];“分别处理，后者视为未初始化使用
						if(varDecl.getType() instanceof CType_Array) {
							String constantxpath=".//UnaryExpression/PostfixExpression/PrimaryExpression/Constant";
							List<SimpleNode> constantList=StateMachineUtils.getEvaluationResults((SimpleNode)((SimpleNode)inialList.get(0)).jjtGetParent().jjtGetParent().jjtGetParent(), constantxpath);
							if(constantList!=null&&constantList.size()>inialList.size())
							return true;
							else 
							return false;
						} else {
							return false;
							
						}
					}
					return true;
				}
			}
		
		}
		return false;
	}
	
	
	/**检测当前变量在没有初始化过就被使用*/
	public static boolean checkUse(VexNode checkedVexNode, FSMMachineInstance fsmInst){
		
		if(checkedVexNode.isBackNode() ){//不对尾节点进行处理
			return false;
		}
		SimpleNode releatedTreeNode = checkedVexNode.getTreenode();	
		
		//如果在该控制流节点上对变量初始化过就不再做使用检查；
		if (/*fsmInst.getReleatedVexNode() == checkedVexNode && */fsmInst.getFlag()){
			
			return false;
		} else if (checkInial(checkedVexNode,fsmInst)){//如果当前节点初始化过就取消该节点跟状态机实例的关联
			fsmInst.setFlag(false);
			fsmInst.setReleatedVexNode(null);
			return false;
		}
		
		//使用检查开始
		String useXpath = ".//UnaryExpression/PostfixExpression[not(./FieldId) and not(./ArgumentExpressionList)]/PrimaryExpression[not(./Constant)]";
		List<SimpleNode> useList = StateMachineUtils.getEvaluationResults(releatedTreeNode,useXpath);
		Iterator<SimpleNode> useItr = useList.iterator();
		while(useItr.hasNext()){
			ASTPrimaryExpression checkedNode = (ASTPrimaryExpression)useItr.next();
			//chh  对于变量的使用也应该检查节点是否可达
			if(checkedNode.getCurrentVexNode() != null && checkedNode.getCurrentVexNode().getContradict()) {
				return false;
				
			}
			//end
			VariableNameDeclaration varDecl = checkedNode.getVariableNameDeclaration();
			if(varDecl == null || varDecl != fsmInst.getRelatedVariable()){
				continue;
			}
			//chh   int i;i&=0x03;类似这样的语句为地址分配，不视为未初始化使用
			if(checkedNode.jjtGetParent().jjtGetParent().jjtGetParent().jjtGetNumChildren()>1)
			{if(checkedNode.jjtGetParent().jjtGetParent().jjtGetParent().jjtGetChild(1) instanceof ASTAssignmentOperator)
			{
				if(((ASTAssignmentOperator)(checkedNode.jjtGetParent().jjtGetParent().jjtGetParent().jjtGetChild(1))).getOperators().equals("&="))
				{
					continue;
				}
			}}
			//end
			//zx: 增加int array[10]; int * p = array;此时的array不算是未初始化，该类问题特殊处理
			//zx: int * p; p = array; 跟上述的AST语法树结构不一样
			if(varDecl.getType() instanceof CType_Array) {
				if(releatedTreeNode instanceof ASTDeclaration) {
					String assignInial = ".//InitDeclaratorList/InitDeclarator/Initializer/AssignmentExpression/UnaryExpression/PostfixExpression[not(./Expression)]/PrimaryExpression[@Image='"+ varDecl.getImage() +"' and not(./Constant)]";
					List<SimpleNode> assignNodeList = StateMachineUtils.getEvaluationResults(releatedTreeNode, assignInial);
					if(assignNodeList != null && assignNodeList.size() > 0) {
						return false;
						}
					} else {
						String assignInial = ".//AssignmentExpression[./AssignmentOperator[@Operators='= ' or @Operators='=']]/AssignmentExpression/UnaryExpression/PostfixExpression[not(./Expression)]/PrimaryExpression[@Image='"+ varDecl.getImage() +"' and not(./Constant)]";
						List<SimpleNode> assignNodeList = StateMachineUtils.getEvaluationResults(releatedTreeNode, assignInial);
						if(assignNodeList != null && assignNodeList.size() > 0) {
							return false;
						}
					}
			}
			//zx: end
					
			SimpleNode parent = checkedNode;
			while (!(parent instanceof ASTStatement)) {
				parent = (SimpleNode)parent.jjtGetParent();
				// 避免形如sizeof(*a)这类误报
				if (parent instanceof ASTUnaryExpression && parent.getImage().equals("sizeof")) {
					return false;
				}
			}
			/**chh  对于**head节点，由于getTreenode()返回整个语句块，如果没有下面的检测，可能在语句块中先使用
			 * 后初始化的情况会漏报，所以要对语句块中变量使用出现及之前的statement节点进行初始化检测，如果变量
			 * 在这些语句中初始化，则跳转end状态，否则报告故障：未初始化使用。
			 * 
			 */
			if(!(checkedVexNode.getName().startsWith("for_head")||checkedVexNode.getName().startsWith("if_head")
					||checkedVexNode.getName().startsWith("while_head")||checkedVexNode.getName().startsWith("do_while_head")))
			{
			fsmInst.setRelatedASTNode(checkedNode);
			fsmInst.setDesp("在第 " + varDecl.getNode().getBeginLine() + " 行定义的变量\""+ varDecl.getImage() + "\"可能未初始化便进行了使用。");		
			return true;
			}
			else
			{
				Node statementList=releatedTreeNode.getFirstChildOfType(ASTStatementList.class);
				Node end=checkedNode.getFirstParentOfType(ASTStatement.class);
				if(statementList==null||statementList.jjtGetNumChildren()==0)
					{
					fsmInst.setRelatedASTNode(checkedNode);
					fsmInst.setDesp("在第 " + varDecl.getNode().getBeginLine() + " 行定义的变量\""+ varDecl.getImage() + "\"可能未初始化便进行了使用。");		
					return true;
					}
				else{
					int i=0;
					for(Node temp=statementList.jjtGetChild(i);i!=statementList.jjtGetNumChildren()&&temp!=end;i++)
					{
						if(isInit(varDecl,(SimpleNode)temp))
						{
							return false;
						}
						else 
							{
							if(isInit(varDecl,(SimpleNode)end)) return false;
							else
								{
								fsmInst.setRelatedASTNode(checkedNode);
								fsmInst.setDesp("在第 " + varDecl.getNode().getBeginLine() + " 行定义的变量\""+ varDecl.getImage() + "\"可能未初始化便进行了使用。");		
								return true;	
								}
							}
					}
				}
			}
		}
		return false;
	}
	
}
