package softtest.rules.gcc.fault;


import java.util.ArrayList;
import java.util.ConcurrentModificationException;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.*;
import softtest.cfg.c.VexNode;
import softtest.fsm.c.*;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.*;
import softtest.symboltable.c.Type.*;



/**
 * @author zl
 * UnInited Variable[未初始化变量]
 * */
public class UVF_ExpStateMachine {
	private static Hashtable<VariableNameDeclaration,VariableNameDeclaration> varTable=new Hashtable<VariableNameDeclaration,VariableNameDeclaration>();
	/**为每个没有初始化的非静态、非外部的局部变量创建状态机*/
	public static List<FSMMachineInstance> createUVF_ExpStateMachines(SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		Hashtable<VariableNameDeclaration, FSMMachineInstance> fsmInsTable = new Hashtable<VariableNameDeclaration, FSMMachineInstance>();
		   
		 //查找当前函数中的所有非静态、非外部类型的局部变量, 没有初始化表达式DeclarationList/
		String xpath = ".//Declaration[./DeclarationSpecifiers[not(./StorageClassSpecifier)]]/InitDeclaratorList/InitDeclarator[not(./Initializer)]/Declarator/DirectDeclarator"; 
		xpath+="| .//ExpressionStatement/Expression/AssignmentExpression[./AssignmentOperator and ./AssignmentExpression/CastExpression/UnaryExpression/PostfixExpression/PrimaryExpression[@Image='malloc' or @Image='realloc']]/UnaryExpression/PostfixExpression/PrimaryExpression";
		xpath+="| .//Declaration[./DeclarationSpecifiers[not(./StorageClassSpecifier)]]/InitDeclaratorList/InitDeclarator[./Initializer/AssignmentExpression//UnaryExpression/PostfixExpression/PrimaryExpression[@Image='malloc' or @Image='realloc' ]]/Declarator/DirectDeclarator";
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		/**为当前赋值后的变量创建状态机实例*/
		Iterator<SimpleNode> itr = evaluationResults.iterator();
		while(itr.hasNext()) {
			SimpleNode snode = itr.next();
			VariableNameDeclaration variable=null;
			if(snode instanceof ASTDirectDeclarator){
				ASTDirectDeclarator primaryNode = (ASTDirectDeclarator)snode;
				variable = primaryNode.getVariableNameDeclaration();
			}else if(snode instanceof ASTPrimaryExpression){
				ASTPrimaryExpression priExp=(ASTPrimaryExpression)snode;
				variable = priExp.getVariableNameDeclaration();
			}
			if(variable == null) {
				continue;
			}
			CType type = variable.getType();
			if(!((type instanceof CType_Struct) || (type instanceof CType_Pointer) || (type instanceof CType_Typedef))){
				continue;
			}
			if(type instanceof CType_Pointer)	{
				if(!((((CType_Pointer)type).getOriginaltype() instanceof CType_Struct) || (((CType_Pointer)type).getOriginaltype() instanceof CType_Typedef))){
					continue;
				}
				if(((CType_Pointer)type).getOriginaltype() instanceof CType_Typedef){
					if(!(((CType_Typedef)((CType_Pointer)type).getOriginaltype()).getOriginaltype() instanceof CType_Struct)){
						continue;
					}
				}
			}
			if(type instanceof CType_Typedef)	{
				if(!(((CType_Typedef)type).getOriginaltype() instanceof CType_Struct)){
					continue;
				}				
			}
			ArrayList<VariableNameDeclaration> variablemems=variable.mems;
			Iterator<VariableNameDeclaration> itrvariablemems=variablemems.iterator();
			while(itrvariablemems.hasNext()){
				//dongyk 20120420 处理并发异常
				try
				{
					VariableNameDeclaration memsvariable=itrvariablemems.next();
					CType memsvariabletype=memsvariable.getType();
					if(memsvariabletype instanceof CType_Struct || (memsvariabletype instanceof CType_Typedef && (((CType_Typedef)memsvariabletype).getOriginaltype() instanceof CType_Struct))){
						ArrayList<VariableNameDeclaration> variablememsmem=memsvariable.mems;
						Iterator<VariableNameDeclaration> itrvariablememsmem=variablememsmem.iterator();
						while(itrvariablememsmem.hasNext()){
							variablemems.add(itrvariablememsmem.next());
						}
					}
				}catch(ConcurrentModificationException eCon)
				{
					break;
				}
			}
			Iterator<VariableNameDeclaration> itrvariablemems1=variablemems.iterator();
			while(itrvariablemems1.hasNext()){
				VariableNameDeclaration memsvariable=itrvariablemems1.next();
				CType memsvariabletype=memsvariable.getType();
				//如果结构体成员变量也是复杂数据类型的话
				if(!(memsvariabletype instanceof CType_BaseType || memsvariabletype instanceof CType_Array || memsvariabletype instanceof CType_Pointer)) {
					continue;
				}
				//数组类型只考虑，数组成员是简单类型的变量
		    	if (memsvariabletype instanceof CType_Array && !(((CType_Array)memsvariabletype).getOriginaltype() instanceof CType_BaseType)) {
		    		continue;
		    	}
		    	//仅为当前函数中局部变量创建状态机实例
		    	if(!(memsvariable.getScope() instanceof LocalScope || memsvariable.getScope() instanceof MethodScope)){
		    		continue;
		    	}
		    	if (memsvariable.isParam()) {
		    		continue;
		    	}
		    	//添加成员变量与其父变量之间的关系
		    	if(!varTable.containsKey(memsvariable)){
		    		varTable.put(memsvariable, variable);
		    	}
		    	if(!(fsmInsTable.containsKey(memsvariable))){
		    		FSMMachineInstance fsmInstance = fsm.creatInstance();
					fsmInstance.setRelatedVariable(memsvariable);
					fsmInstance.setRelatedASTNode(snode);
					fsmInsTable.put(memsvariable, fsmInstance);
					list.add(fsmInstance);
			}
		}
		}
		return list;
	}
	
	/**检测控制流节点上是否包含状态机相关的变量*/
	public static boolean checkSameVariable(List<Node> nodeList, FSMMachineInstance fsmInst) {
		Iterator<Node> listItr = nodeList.iterator();
		while(listItr.hasNext()) {
			SimpleNode checkNode=(SimpleNode)listItr.next();
			VariableNameDeclaration variable = checkNode.getVariableNameDeclaration(); 
			if(variable != null && variable ==  (fsmInst.getRelatedASTNode()).getVariableNameDeclaration() && checkNode == fsmInst.getRelatedASTNode()) {
				//VariableNameDeclaration aavariable = fsmInst.getRelatedVariable();
				//ASTDirectDeclarator aacheckNode =(ASTDirectDeclarator) fsmInst.getRelatedASTNode();
				//if(checkNode!=aacheckNode)
					//return false;
				//VariableNameDeclaration aabbvariable= ((ASTDirectDeclarator) fsmInst.getRelatedASTNode()).getVariableNameDeclaration();
				return true;
			}			
		}
		return false;
	}
	
	/**检测状态机相关变量是否被初始化*/
	public static boolean checkInial(VexNode checkedVexNode, FSMMachineInstance fsmInst) {
		
		//chh  对于**head节点暂时认为未初始化，因为getTreenode()返回整个语句块，在后面的checkUse函数中处理
		SimpleNode releatedTreeNode = checkedVexNode.getTreenode();
		if(checkedVexNode.isBackNode()||
				checkedVexNode.getName().startsWith("for_head")||checkedVexNode.getName().startsWith("if_head")
				||checkedVexNode.getName().startsWith("while_head")||checkedVexNode.getName().startsWith("do_while_head")
				||checkedVexNode.getName().startsWith("switch_head")||checkedVexNode.getName().startsWith("label_head_case")){//不对尾节点进行处理
			String mayinitxpath = "./Expression";
			List<SimpleNode> mayinitList = StateMachineUtils.getEvaluationResults(releatedTreeNode,mayinitxpath);
			for( SimpleNode tnode : mayinitList){			
				ASTExpression checkExp = (ASTExpression)tnode;
				if(isInit(fsmInst.getRelatedVariable(), checkExp)){
					fsmInst.setFlag(true);
					fsmInst.setReleatedVexNode(checkedVexNode);
					return true;
				}
			}
			return false;
		}
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
		if(varDecl==null){
			return false;
		}
		//add by zl 20120904,添加成员变量的父变量，减小初始化判断的粒度
		if(!varTable.containsKey(varDecl)){
			return false;
		}
		VariableNameDeclaration varDeclParent=varTable.get(varDecl);
		if(null==varDeclParent){
			return false;
		}
		String varDeclName=varDecl.getImage();
		if(varDeclName==null){
			return false;
		}
		String mainVarName=varDeclName.split("->")[0];
		/**看节点是否对结构体变量整体进行初始化*/
		String mainVarXpath=".//Expression/AssignmentExpression[./AssignmentOperator]/UnaryExpression/PostfixExpression/PrimaryExpression[@Image='"+mainVarName+"']";
		List<SimpleNode> mainVarList = StateMachineUtils.getEvaluationResults(node,mainVarXpath);	
		if(mainVarList!=null && mainVarList.size()>0){
			return true;
		}
		
		//step1通过系统函数初始化
		
		//step1.1: 通过函数sscanf( const char *, const char *, ...);进行初始化
		String ioInialXpath = ".//PostfixExpression[./PrimaryExpression[@Image='sscanf']]/ArgumentExpressionList/AssignmentExpression[last()]//PostfixExpression[not(./Expression)]/PrimaryExpression[count(*)=0]";
		List<SimpleNode> cinList = StateMachineUtils.getEvaluationResults(node,ioInialXpath);	
		for( SimpleNode tnode : cinList){			
			ASTPostfixExpression checkExp = (ASTPostfixExpression)(tnode.jjtGetParent());
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
		String memsetXpath=".//PostfixExpression[./ArgumentExpressionList[count(*)=3]]/PrimaryExpression[@Image='memset']";
		List<SimpleNode> memsetList= StateMachineUtils.getEvaluationResults(node,memsetXpath);	
		for(SimpleNode tnode:memsetList){
			ASTPostfixExpression checkExp = (ASTPostfixExpression)(tnode.jjtGetParent());
			if(checkExp.getCurrentVexNode() != null && checkExp.getCurrentVexNode().getContradict()) {
				return false;
			}
			String aaxpath=".//UnaryExpression/PostfixExpression[@Image='"+varDecl.getNode().getImage()+"']";
			List<SimpleNode> aaList= StateMachineUtils.getEvaluationResults((SimpleNode)checkExp.jjtGetChild(1).jjtGetChild(0),aaxpath);	
			if(aaList!=null && aaList.size()>0){
				return true;
			}
		}
		//step1.2 先除掉strcpy(dest,src)中第二个元素不对其进行初始化；
		//同理strncpy(dest,src)不对其第二个元素进行初始化，当变量作为第二个参数传入时，返回false
		//step1.3 同理，也应该除去strcmp(str1, str2)、strstr(str1, str2)，其中两个参数都应该初始化
		String defaultFunList[] = {"strcpy", "strncpy","memcpy", "memmove", "strcat", "strncat"};
		String cmpFuncList[] = {"strstr", "strcmp", "strncmp", "memcmp"};
		  
		String ioNoInialxPath=".//PostfixExpression[./ArgumentExpressionList[count(*)=2]/AssignmentExpression/UnaryExpression/PostfixExpression[@Image='"+varDecl.getImage()+"']]/PrimaryExpression";
		//String ioNoInialxPath=".//PostfixExpression[./ArgumentExpressionList[count(*)=2]/AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression[@Image='"+varDecl.getImage()+"']]/PrimaryExpression";
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
					//zys:2010.7.22	
					if(list.size()>0){
						SimpleNode arg1 = list.get(0);
						SimpleNode aaarg1=(SimpleNode)arg1.jjtGetParent();
						if(aaarg1.getImage().equals(varDecl.getImage())) {
							return false;
						}
					}
				}
			}
			for(String name : cmpFuncList) {
				if(funcName.equals(name)) {
					List<SimpleNode>  list = StateMachineUtils.getEvaluationResults(expList, "./AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression");
					SimpleNode arg = list.get(0);//变量位于第一形参的位置
					SimpleNode aaarg=(SimpleNode)arg.jjtGetParent();
					if(aaarg.getImage().equals(varDecl.getImage())) {
						return false;
					}
					arg = list.get(1);//变量位于第二形参的位置
					SimpleNode aarg=(SimpleNode)arg.jjtGetParent();
					if(aarg.getImage().equals(varDecl.getImage())) {
						return false;
					}
				}
			}
			return true;
		}
		//step1.2_end
		
		
		// step2.1: 通过函数调用进行初始化，如果将变量取地址做参数传入函数中，则默认该变量由当前函数进行初始化
		// 形如: func(&a); scanf("%d", &a); func(&a, 1);两者语法树稍有不同，C++特定的语法造成(此处语法无区别)
		String xPath = ".//PostfixExpression[./PrimaryExpression]/ArgumentExpressionList/AssignmentExpression/UnaryExpression[./UnaryOperator[@Operators='&']]/UnaryExpression/PostfixExpression";///PrimaryExpression";
		funInialList = StateMachineUtils.getEvaluationResults(node, xPath);
		for (SimpleNode idExp : funInialList) {
			ASTPostfixExpression snode = (ASTPostfixExpression)idExp;
			//zx: 判断该节点可达否，不可达直接返回false
			if(idExp.getCurrentVexNode()!= null && idExp.getCurrentVexNode().getContradict()) {
				//return false;
				continue;
			}
			if (snode.getVariableNameDeclaration() != null) {
				if (snode.getVariableNameDeclaration() == varDeclParent || snode.getVariableNameDeclaration() == varDecl) {
					return true;
				}
			}
		}
		
		
		//step2.2: 通过函数调用进行初始化， 如果将变量传引用，则默认该变量由当前函数进行初始化
		//声明void func(int &i, int b);
		//当调用func(i, 0);时默认为对i进行了初始化(无传引用)
		//step2.3: int * array;或者 int array[10];时
		//func(array, b);传入时，array为指针类型，视为func函数将其初始化
		xPath=".//PostfixExpression[./ArgumentExpressionList/AssignmentExpression//UnaryExpression/PostfixExpression[@Image='" + varDecl.getImage() + "']]/PrimaryExpression";
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
			String inialExpressionXpath = "./UnaryExpression/PostfixExpression[@Image='"+ varDecl.getImage() +"' or @Image='"+varDeclParent.getImage()+"']";
			List<SimpleNode> inialExpList = StateMachineUtils.getEvaluationResults(assignNode, inialExpressionXpath);
			Iterator<SimpleNode> itr = inialExpList.iterator();
			while(itr.hasNext()){
			ASTPostfixExpression idExp = (ASTPostfixExpression) itr.next();
			if (idExp.getVariableDecl() != null) {
				if (idExp.getVariableDecl().equals(varDecl)) {
					//zx: 判断‘=’右边是否也出现了同一个变量，如i = i + 1;
					//小心int i; i = a.i;此类问题。故不能直接.//id_expression，会引来误报
					String sameVariableXpath = ".//UnaryExpression/PostfixExpression[@Image='"+ varDecl.getImage() +"' and count(*)= 0]";
					List<SimpleNode> inialList = StateMachineUtils.getEvaluationResults((SimpleNode)assignNode.jjtGetChild(2), sameVariableXpath);
					if(inialList != null && inialList.size() > 0) {
						//chh: 判断‘=’右边是否也出现了同一个变量，如array[1] = array[0] = 0;
						//添加判断，对”array[1] = array[0] = 0;“和”array[1] = array[0];“分别处理，后者视为未初始化使用
						if(varDecl.getType().isPointType()) {
							String othervarxpath=".//UnaryExpression/PostfixExpression[@Image!='"+ varDecl.getImage() +"' ]";
							List<SimpleNode> constantList=StateMachineUtils.getEvaluationResults((SimpleNode)((SimpleNode)inialList.get(0)).jjtGetParent().jjtGetParent(), othervarxpath);
							if(constantList!=null&&constantList.size()>inialList.size())
								return true;
							else {
								String funpath=".//UnaryExpression[@Image='sizeof' and @Image='strlen']//UnaryExpression/PostfixExpression[@Image='"+ varDecl.getImage() +"' and count(*)= 0]";
								List<SimpleNode> funList =StateMachineUtils.getEvaluationResults((SimpleNode)assignNode.jjtGetChild(2), funpath);
								if(funList!=null&&funList.size()>=inialList.size())
									return  true;
								else 
									return false;
							}
							
						} else {
							return false;
							
						}
					}
					return true;
				}else if(idExp.getVariableDecl().equals(varDeclParent)){
					return true;
				}
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
		if (fsmInst.getFlag()){
			
			return false;
		} else if (checkInial(checkedVexNode,fsmInst)){//如果当前节点初始化过就取消该节点跟状态机实例的关联
			fsmInst.setFlag(false);
			fsmInst.setReleatedVexNode(null);
			return false;
		}
		
		//使用检查开始
		//String useXpath = ".//UnaryExpression/PostfixExpression[not(./FieldId) and not(./ArgumentExpressionList)]/PrimaryExpression[not(./Constant)]";
		String useXpath=".//UnaryExpression/PostfixExpression[./FieldId and not(./ArgumentExpressionList) and not(./Constant) and ./PrimaryExpression[@DescendantDepth='0']]";//结构体成员的使用节点
		List<SimpleNode> useList = StateMachineUtils.getEvaluationResults(releatedTreeNode,useXpath);
		Iterator<SimpleNode> useItr = useList.iterator();
out:	while(useItr.hasNext()){
			ASTPostfixExpression checkedNode = (ASTPostfixExpression)useItr.next();
			//chh  对于变量的使用也应该检查节点是否可达
			if(checkedNode.getCurrentVexNode() != null && checkedNode.getCurrentVexNode().getContradict()) {
				continue;
				
			}
			//end
			if(checkedNode.jjtGetChild(1) instanceof ASTFieldId){
				VariableNameDeclaration varDecl =((ASTFieldId)(checkedNode.jjtGetChild(1))).getVariableNameDeclaration();
				String varImage=checkedNode.getImage();
				String relatedVariableImage=fsmInst.getRelatedVariable().getImage();
				if(varImage == null || !(varImage.equals(relatedVariableImage))){
					continue;
				}
				//chh   int i;i&=0x03;类似这样的语句为地址分配，不视为未初始化使用
				if(checkedNode.jjtGetParent().jjtGetParent().jjtGetNumChildren()>1)
				{if(checkedNode.jjtGetParent().jjtGetParent().jjtGetChild(1) instanceof ASTAssignmentOperator)
				{
					if(((ASTAssignmentOperator)(checkedNode.jjtGetParent().jjtGetParent().jjtGetChild(1))).getOperators().equals("&="))
					{
						continue;
					}
				}}
				//end
				SimpleNode parent = (SimpleNode) checkedNode.getFirstParentOfType(ASTUnaryExpression.class);
				if(parent!=null&&parent.jjtGetParent() instanceof ASTUnaryExpression ){
					String opxpath = "./UnaryOperator[@Operators='&']";
					if(StateMachineUtils.getEvaluationResults((SimpleNode) parent.jjtGetParent(), opxpath)!=null)
						continue;
				}
				//zx: 增加int array[10]; int * p = array;此时的array不算是未初始化，该类问题特殊处理
				//zx: int * p; p = array; 跟上述的AST语法树结构不一样
				if(varDecl!=null && varDecl.getType() instanceof CType_Array) {
					if(releatedTreeNode instanceof ASTDeclaration) {
						//String assignInial = ".//InitDeclaratorList/InitDeclarator/Initializer/AssignmentExpression/UnaryExpression/PostfixExpression[not(./Expression)]/PrimaryExpression[@Image='"+ varDecl.getImage() +"' and not(./Constant)]";
						String assignInial = ".//InitDeclaratorList/InitDeclarator/Initializer/AssignmentExpression/UnaryExpression/PostfixExpression[not(./Expression) and @Image='"+ varDecl.getImage() +"' and ./PrimaryExpression[@DescendantDepth='0']]";
						List<SimpleNode> assignNodeList = StateMachineUtils.getEvaluationResults(releatedTreeNode, assignInial);
						if(assignNodeList != null && assignNodeList.size() > 0) {
							continue;
							}
						} else {
							String assignInial = ".//AssignmentExpression[./AssignmentOperator[@Operators='= ' or @Operators='=']]/AssignmentExpression//UnaryExpression/PostfixExpression[not(./Expression) and @Image='"+ varDecl.getImage() +"' and ./PrimaryExpression[@DescendantDepth='0']]";
							List<SimpleNode> assignNodeList = StateMachineUtils.getEvaluationResults(releatedTreeNode, assignInial);
							if(assignNodeList != null && assignNodeList.size() > 0) {
								continue;
							}
						}
				}
				//zx: end
						
				parent = checkedNode;
				while (!(parent instanceof ASTStatement)) {
					parent = (SimpleNode)parent.jjtGetParent();
					// 避免形如sizeof(*a)这类误报
					if (parent instanceof ASTUnaryExpression && parent.getImage().equals("sizeof")) {
						continue out;
					}
				}
				/**chh  对于**head节点，由于getTreenode()返回整个语句块，如果没有下面的检测，可能在语句块中先使用
				 * 后初始化的情况会漏报，所以要对语句块中变量使用出现及之前的statement节点进行初始化检测，如果变量
				 * 在这些语句中初始化，则跳转end状态，否则报告故障：未初始化使用。
				 * 
				 */
				
				if(!(checkedVexNode.getName().startsWith("for_head")||checkedVexNode.getName().startsWith("if_head")
						||checkedVexNode.getName().startsWith("while_head")||checkedVexNode.getName().startsWith("do_while_head")
						||checkedVexNode.getName().startsWith("switch_head")||checkedVexNode.getName().startsWith("label_head_case"))
						&&(checkedNode.getFirstParentOfType(ASTSelectionStatement.class)==null&&checkedNode.getFirstParentOfType(ASTIterationStatement.class)==null))
				{
				fsmInst.setRelatedASTNode(checkedNode);
				fsmInst.setDesp("在第 " + fsmInst.getRelatedASTNode().getBeginLine()+ " 行的复杂结构变量\""+ ((ASTPrimaryExpression)checkedNode.jjtGetChild(0)).getImage()+ "\"的成员变量\""+ varImage + "\"可能未初始化便进行了使用。");		
				return true;
				}
				else if(checkedVexNode.getName().startsWith("while_head")){
					parent = (SimpleNode) checkedNode.jjtGetParent();
					while (parent != releatedTreeNode){
						parent = (SimpleNode) parent.jjtGetParent();
						if(releatedTreeNode.jjtGetChild(0) instanceof ASTExpression && parent == releatedTreeNode.jjtGetChild(0)){
							fsmInst.setRelatedASTNode(checkedNode);
							fsmInst.setDesp("在第 " + fsmInst.getRelatedASTNode().getBeginLine()+ " 行的复杂结构变量\""+ ((ASTPrimaryExpression)checkedNode.jjtGetChild(0)).getImage()+ "\"的成员变量\""+ varImage + "\"可能未初始化便进行了使用。");		
							return true;
						}
							
					}
					continue;
				}
				else if(!(checkedVexNode.getName().startsWith("for_head")||checkedVexNode.getName().startsWith("if_head")
						||checkedVexNode.getName().startsWith("while_head")||checkedVexNode.getName().startsWith("do_while_head")
						||checkedVexNode.getName().startsWith("switch_head")||checkedVexNode.getName().startsWith("label_head_case"))
						&&(checkedNode.getFirstParentOfType(ASTSelectionStatement.class)!=null||checkedNode.getFirstParentOfType(ASTIterationStatement.class)!=null)){
					releatedTreeNode = (SimpleNode) ((checkedNode.getFirstParentOfType(ASTSelectionStatement.class)!=null)?checkedNode.getFirstParentOfType(ASTSelectionStatement.class):checkedNode.getFirstParentOfType(ASTIterationStatement.class));
					Node statementList=releatedTreeNode.getFirstChildOfType(ASTStatementList.class);
					Node end=checkedNode.getFirstParentOfType(ASTStatement.class);
					if(statementList==null||statementList.jjtGetNumChildren()==0)
						{
						fsmInst.setRelatedASTNode(checkedNode);
						fsmInst.setDesp("在第 " + fsmInst.getRelatedASTNode().getBeginLine()+ " 行的复杂结构变量\""+ ((ASTPrimaryExpression)checkedNode.jjtGetChild(0)).getImage()+ "\"的成员变量\""+ varImage + "\"可能未初始化便进行了使用。");		
						return true;
						}
					else{
					
					for(int i=0;i!=statementList.jjtGetNumChildren();i++)
					{
						Node temp=statementList.jjtGetChild(i);
						if(temp == end ) 
							{
								fsmInst.setRelatedASTNode(checkedNode);
								String expVar=null;
								if(((ASTPrimaryExpression)checkedNode.jjtGetChild(0))!=null){
									expVar=((ASTPrimaryExpression)checkedNode.jjtGetChild(0)).getImage();
								}
								fsmInst.setDesp("在第 " + fsmInst.getRelatedASTNode().getBeginLine()+ " 行的复杂结构变量\""+ expVar+ "\"的成员变量\""+ varImage + "\"可能未初始化便进行了使用。");		
								return true;
							}
						if(isInit(varDecl,(SimpleNode)temp))
						{
							continue out;
						}

					}
				}
				}
			}
		}
		return false;
	}

}

