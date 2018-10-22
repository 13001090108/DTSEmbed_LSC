package softtest.rules.gcc.fault;

import java.util.*;

import softtest.ast.c.*;
import softtest.cfg.c.VexNode;
import softtest.domain.c.analysis.ExpressionValueVisitor;
import softtest.domain.c.analysis.ExpressionVistorData;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.IntegerDomain;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.interpro.c.InterContext;
import softtest.rules.c.BasicStateMachine;
import softtest.rules.c.StateMachineUtils;
import softtest.summary.gcc.fault.MethodUVF_PPreCondition;
import softtest.summary.gcc.fault.MethodUVF_PPreConditionVisitor;
import softtest.summary.gcc.fault.UVF_PInfo;
import softtest.summary.gcc.fault.UVF_PInfo.UVF_PType;
import softtest.symboltable.c.*;
import softtest.symboltable.c.Type.*;

/**
 * @author zl UnInited Variable_Pointer 只考虑简单的声明为指针变量
 */
public class UVF_PStateMachine extends BasicStateMachine {
	private static Set<VariableNameDeclaration> initedAsOne = null;
	private static Set<VariableNameDeclaration> inited = null;
	private static Set<UVF_PCheckInfo> initedVariable=null;
	
	@Override
	public void registFetureVisitors() {
		super.registFetureVisitors();
		InterContext.addPreConditionVisitor(MethodUVF_PPreConditionVisitor.getInstance());
	}

	/** 为每个没有初始化的非静态、非外部的局部变量创建状态机 */
	public static List<FSMMachineInstance> createUVF_PStateMachines(SimpleNode node, FSMMachine fsm) {
		initedVariable=new HashSet<UVF_PCheckInfo>();
		initedAsOne = new HashSet<VariableNameDeclaration>();
		inited = new HashSet<VariableNameDeclaration>();
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		Hashtable<VariableNameDeclaration, FSMMachineInstance> fsmInsTable = new Hashtable<VariableNameDeclaration, FSMMachineInstance>();
		/** 查找当前函数中的所有非静态、非外部类型的被使用的局部指针变量和局部数组变量 */
		String xpath = ".//InitDeclarator[(.//Initializer/AssignmentExpression//UnaryExpression/PostfixExpression/PrimaryExpression[@Image='malloc'])]/Declarator[(./Pointer)]/DirectDeclarator | .//InitDeclarator[count(*)=1]/Declarator[(./Pointer)]/DirectDeclarator";
		xpath += "|.//Declaration[./DeclarationSpecifiers[not(./StorageClassSpecifier)]]/InitDeclaratorList/InitDeclarator[not(./Initializer)]/Declarator/DirectDeclarator[count(*)!=0]"; 
		xpath+="| .//Declaration[./DeclarationSpecifiers[not(./StorageClassSpecifier)]]/InitDeclaratorList/InitDeclarator[./Initializer/AssignmentExpression/CastExpression//UnaryExpression/PostfixExpression/PrimaryExpression[@Image='malloc' or @Image='realloc']]/Declarator/DirectDeclarator[count(*)!=0]";
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		Iterator<SimpleNode> Itr = evaluationResults.iterator();
		while (Itr.hasNext()) {
			SimpleNode checkNode = Itr.next();
			if (null == checkNode|| (checkNode.getCurrentVexNode() != null && checkNode.getCurrentVexNode().getContradict())) {
				continue;
			}
			VariableNameDeclaration variable = checkNode.getVariableNameDeclaration();
			if (variable == null || variable.isParam()) {
				continue;
			}
			if (!(variable.getScope() instanceof LocalScope || variable
					.getScope() instanceof MethodScope)) {
				continue;
			}
			CType type = variable.getType();
			if (null == type
					|| !(type instanceof CType_Pointer || type instanceof CType_Array)
					&& !(type.getSimpleType() instanceof CType_BaseType)) {
				continue;
			}
			if (!(fsmInsTable.containsKey(variable))) {
				FSMMachineInstance fsmInstance = fsm.creatInstance();
				fsmInstance.setRelatedVariable(variable);
				fsmInstance.setRelatedASTNode(checkNode);
				fsmInsTable.put(variable, fsmInstance);
				list.add(fsmInstance);
			}
		}
		return list;
	}

	/** 检测状态机相关变量是否被初始化 */
	public static int checkInial(VexNode checkedVexNode,FSMMachineInstance fsmInst) {
		SimpleNode releatedTreeNode = checkedVexNode.getTreenode();
		if (checkedVexNode.isBackNode()
				|| checkedVexNode.getName().startsWith("for_head")
				|| checkedVexNode.getName().startsWith("if_head")
				|| checkedVexNode.getName().startsWith("while_head")
				|| checkedVexNode.getName().startsWith("do_while_head")
				|| checkedVexNode.getName().startsWith("switch_head")
				|| checkedVexNode.getName().startsWith("label_head_case")) {
			/** 不对尾节点进行处理 */
			String mayInialXpath = "./Expression";
			List<SimpleNode> mayInialList = StateMachineUtils.getEvaluationResults(releatedTreeNode, mayInialXpath);
			Iterator<SimpleNode> mayInialItr = mayInialList.iterator();
			int result=-1;
			while (mayInialItr.hasNext()) {
				result=checkAsOneMay(fsmInst.getRelatedVariable(), mayInialItr.next());
				if (result!=-1) {
					return result;
				}
			}
			return result;
		}
		return checkAsOne(fsmInst.getRelatedVariable(), releatedTreeNode);
	}

	/**
	 * 检测状态机相关变量是否被初始化 仅仅处理循环语句的尾节点while_out、for_out
	 * 假定能够进入while/for循环，并且变量在其中初始化了，出循环后，默认为该变量已初始
	 * 如果该方法不存在，只存在上述的checkInial，因为UVF被认为是路径敏感
	 * ，所以可能会认为有一条没有进while循环的路径，导致误报（路径铭感不会导致漏报的） 加该方法的目的仅仅是减少因为循环语句引起的太多误报
	 * */
	public static boolean checkArrayInial(VexNode checVexNode,FSMMachineInstance fsmInst) {
		if (!(checVexNode.getName().startsWith("for_out") || checVexNode.getName().startsWith("while_out"))) {
			return false;
		}
		SimpleNode releatedTreeNode = checVexNode.getTreenode();
		VariableNameDeclaration variable = fsmInst.getRelatedVariable();
		int result=checkAsOne(variable, releatedTreeNode);
		switch(result){
		case 1://初始化
			if(!initedAsOne.contains(variable)){
				initedAsOne.add(variable);	
			}
			fsmInst.setFlag(true);
			return true;
		}
		return false;
	}

	public static int checkAsOneMay(VariableNameDeclaration variable,SimpleNode node) {
		String varImage = variable.getImage();
		if (null == varImage || varImage.equals("")) {
			return -1;
		}
		/**检查等式*/
		int i=checkEqualExpression(node,variable,varImage);
		if(i!=-1){
			return i;
		}
		/**检查函数表达式*/
		i=checkFunctionExpression(node,variable,varImage);
		if(i!=-1){
			return i;
		}
		return i;
	}
	/**
	 * 检测指针变量的内存域变量是否作为整体被初始化 为了减少误报，对指针变量重新分配内存空间或者释放指针变量为游离状态，也认为指针变量已经被整体初始化
	 * @return int -1|0|1|2 : 其他|使用|初始化|重新分配内存(包括：游离)
	 */
	public static int checkAsOne(VariableNameDeclaration variable,SimpleNode node) {
		VexNode vexNode = node.getCurrentVexNode();
		SimpleNode treeNode = vexNode.getTreenode();
		String varImage = variable.getImage();
		if (null == treeNode || null == varImage || varImage.equals("")) {
			return -1;
		}
		/**检查等式*/
		int i=checkEqualExpression(treeNode,variable,varImage);
		if(i!=-1){
			return i;
		}
		/**检查函数表达式*/
		i=checkFunctionExpression(treeNode,variable,varImage);
		if(i!=-1){
			return i;
		}
		return i;
	}
	/**
	 * 检查函数表达式
	 * @param treeNode
	 * @param variable
	 * @param varImage
	 * @return int -1|0|1|2 : 其他|使用|初始化|重新分配内存(包括：游离)
	 */
	public static int checkFunctionExpression(SimpleNode simpleNode,VariableNameDeclaration variable, String varImage) {
		//scanf，sscanf
		String xpath = ".//PostfixExpression[(./PrimaryExpression[@Image='scanf' or @Image='sscanf'])]//ArgumentExpressionList/AssignmentExpression[last()]/UnaryExpression/PostfixExpression[count(*)=1]/PrimaryExpression[@Image='"+varImage+"']";
		List<SimpleNode> list = StateMachineUtils.getEvaluationResults(simpleNode, xpath);
		if(list!=null && list.size()>0) {
			return 1;
		}
		//第一参数为初始化，第二参数为使用
		String funcList[] = { "sprintf","fgets","strcpy", "strncpy", "memset","memcpy", "memmove","strcat", "strncat" };
		xpath = ".//PostfixExpression[./ArgumentExpressionList[count(*)>=2]/AssignmentExpression/UnaryExpression/PostfixExpression[count(*)=1]/PrimaryExpression[@Image='"+varImage+"']]/PrimaryExpression";
		list = StateMachineUtils.getEvaluationResults(simpleNode, xpath);
		String funcName;
		for(SimpleNode snode:list){
			if(snode.jjtGetParent().jjtGetNumChildren()<2){
				continue;
			}
			SimpleNode expList = (SimpleNode)snode.jjtGetParent().jjtGetChild(1);
			if (null==expList) {
				continue;
			}
			funcName = ((ASTPrimaryExpression)snode).getImage();			
			for(String name : funcList) {
				if(funcName.equals("fgets")){
					if(expList.jjtGetNumChildren()<3){
						continue;
					}
					//第三参数使用
					List<SimpleNode>  paramlist = StateMachineUtils.getEvaluationResults(expList, "./AssignmentExpression[3]/UnaryExpression/PostfixExpression[count(*)=1]/PrimaryExpression[@Image='"+varImage+"']");
					if(null!=paramlist && paramlist.size()>0){
							return 0;
					}
					//第一参数初始化
					paramlist = StateMachineUtils.getEvaluationResults(expList, "./AssignmentExpression[1]/UnaryExpression/PostfixExpression[count(*)=1]/PrimaryExpression[@Image='"+varImage+"']");
					if(null!=paramlist && paramlist.size()>0){
							return 1;
					}
				}
				if(funcName.equals(name)) {
					
					if(expList.jjtGetNumChildren()<2){
						continue;
					}
					//第二参数
					List<SimpleNode>  paramlist = StateMachineUtils.getEvaluationResults(expList, "./AssignmentExpression[2]/UnaryExpression/PostfixExpression[count(*)=1]/PrimaryExpression[@Image='"+varImage+"']");
					if(null!=paramlist && paramlist.size()>0){
							return 0;
					}
					//第一参数
					paramlist = StateMachineUtils.getEvaluationResults(expList, "./AssignmentExpression[1]/UnaryExpression/PostfixExpression[count(*)=1]/PrimaryExpression[@Image='"+varImage+"']");
					if(null!=paramlist && paramlist.size()>0){
							return 1;
					}
				}
			}
		}
		return -1;
	}

	/**
	 * 检测等式
	 * @param treeNode
	 * @param variable
	 * @param varImage
	 * @return int -1|0|1|2: 其他|使用|初始化|重新分配内存(包括：游离)
	 */
	public static int checkEqualExpression(SimpleNode treeNode,VariableNameDeclaration variable, String varImage) {
		String checkXpath=".//AssignmentExpression[./AssignmentOperator[@Operators='= ' or @Operators='=']]";
		List<SimpleNode> checkList=StateMachineUtils.getEvaluationResults(treeNode, checkXpath);
		Iterator<SimpleNode> checkItr=checkList.iterator();
		while(checkItr.hasNext()){
			ASTAssignmentExpression assignNode=(ASTAssignmentExpression)checkItr.next();
			if(null==assignNode || assignNode.jjtGetNumChildren()!=3){
				continue;
			}
			String leftXpath=".//PostfixExpression[count(*)=1]/PrimaryExpression[@Image='"+ varImage + "' ]";
			List<SimpleNode> leftList=StateMachineUtils.getEvaluationResults((SimpleNode)(assignNode.jjtGetChild(0)), leftXpath);
			if(null==leftList || 0==leftList.size()){
				//等式左边没有指针变量
				ASTAssignmentExpression rightExp=(ASTAssignmentExpression) assignNode.jjtGetChild(2);
				if(null==rightExp){
					continue;
				}else if(1==rightExp.jjtGetNumChildren()){
					//等式左边没有指针变量，等式右边的指针变量情况
					int i=checkRightEqualAsOneWithoutLeft(rightExp,variable,varImage);
					if(i!=-1){
						return i;
					}
				}else if(3==rightExp.jjtGetNumChildren()){
					//检测特殊情况，等式右边还有等式嵌套的情况，如 int* a=p=c;
					if(rightExp.jjtGetChild(1) instanceof ASTAssignmentOperator && ((ASTAssignmentOperator)rightExp.jjtGetChild(1)).getImage().equals("=")){
						//检测指针变量是否出现在嵌套等式的左边
						List<SimpleNode> equalList=StateMachineUtils.getEvaluationResults((SimpleNode)(rightExp.jjtGetChild(0)), leftXpath);
						if(null!=equalList && equalList.size()>0){
							//指针出现在嵌套等式的左边
							int i=checkRightEqualAsOneWithLeft((SimpleNode)rightExp.jjtGetChild(2),variable,varImage);
							if(i!=-1){
								return i;
							}
						}
					}
				}
			}else{
				//等式左边有指针变量出现，检测等式右边
				int i=checkRightEqualAsOneWithLeft((SimpleNode)assignNode.jjtGetChild(2),variable,varImage);
				if(i!=-1){
					return i;
				}
			}
		}
		return -1;
	}

	/**
	 * 检测等式右边指针变量整体的使用初始化,等式左边含有指针变量
	 * @param simpleNode
	 * @param variable
	 * @return int -1|0|1|2: 其他|使用|初始化|重新分配内存(包括：游离)
	 */
	private static int checkRightEqualAsOneWithLeft(SimpleNode simpleNode,VariableNameDeclaration variable,String varImage) {
		String xpath = ".//UnaryExpression/PostfixExpression[count(*)=1]/PrimaryExpression[@Image='"+ varImage + "' ]";
		List<SimpleNode> list = StateMachineUtils.getEvaluationResults(simpleNode, xpath);
		//等式右边无指针变量出现
		if(null==list || list.size()==0){
			String reallocXpath="./UnaryExpression/PostfixExpression/PrimaryExpression[@Image='malloc' or @Image='realloc']";
			reallocXpath+="| ./CastExpression//UnaryExpression/PostfixExpression/PrimaryExpression[@Image='malloc' or @Image='realloc']";
			List<SimpleNode> reallocList = StateMachineUtils.getEvaluationResults(simpleNode, reallocXpath);
			if(null!=reallocList && reallocList.size()>0){
				return 2;
			}
			return 1;
		}
		//等式右边有指针变量出现
		Iterator<SimpleNode> equalItr = list.iterator();
		while (equalItr.hasNext()) {
			SimpleNode checkNode = equalItr.next();
			//realloc情况，特殊情况下a=(int *)realloc(p,10*sizeof(int));
			String reallocXpath = ".//UnaryExpression/PostfixExpression[./PrimaryExpression[@Image='realloc']]/ArgumentExpressionList//UnaryExpression/PostfixExpression[count(*)=1]/PrimaryExpression[@Image='"+ varImage + "' ]";
			List<SimpleNode> reallocList = StateMachineUtils.getEvaluationResults(simpleNode,reallocXpath);
			Iterator<SimpleNode> reallocItr=reallocList.iterator();
			while(reallocItr.hasNext()){
				if(checkNode.equals(reallocItr.next())){
					return 2;
				}
			}
		}
		return -1;
	}

	/**
	 * 检测等式右边指针变量整体的使用初始化，等式左边没有指针变量
	 * @param simpleNode
	 * @param variable
	 * @return int -1|0|1|2: 其他|使用|初始化|重新分配内存(包括：游离)
	 */
	public static int checkRightEqualAsOneWithoutLeft(SimpleNode simpleNode,VariableNameDeclaration variable,String varImage) {
		/**检测realloc情况*/
		String reallocXpath = ".//UnaryExpression/PostfixExpression[./PrimaryExpression[@Image='realloc']]/ArgumentExpressionList/AssignmentExpression[1]//UnaryExpression/PostfixExpression[count(*)=1]/PrimaryExpression[@Image='"+ varImage + "' ]";
		List<SimpleNode> reallocList=StateMachineUtils.getEvaluationResults(simpleNode, reallocXpath);
		if(null!=reallocList && reallocList.size()>0){
			return 2;
		}
		return -1;
	}

	/** 检测当前指针变量的内存与变量在没有初始化过就被使用 */
	public static boolean checkUse(VexNode vexNode, FSMMachineInstance fsmInst) {
		/** 不对尾节点进行处理 */
		if (vexNode.isBackNode()) {
			return false;
		}
		SimpleNode treeNode = vexNode.getTreenode();
		VariableNameDeclaration variable=fsmInst.getRelatedVariable();
		if (null == treeNode || null==variable) {
			return false;
		}
		String varImage = variable.getImage();
		/** 如果在该控制流节点上对指针变量整体初始化过就不再做使用检查 */ 
		if (null == varImage || varImage.equals("") || fsmInst.getFlag()) {
			return false;
		}
		for(UVF_PCheckInfo inited:initedVariable){
			if(varImage.equals(inited.getVariable().getImage()) && inited.isInitedAsOne()){
				return false;
			}
		}
		int result=checkInial(vexNode, fsmInst);
		switch(result){
		case 0://使用
			boolean flag=false;
			for(UVF_PCheckInfo inited:initedVariable){
				if(varImage.equals(inited.getVariable().getImage())){
					flag=true;
					break;
				}
			}
			if(!flag){
			fsmInst.setRelatedASTNode(treeNode);
			fsmInst.setDesp("在第 " + variable.getNode().getBeginLine() + " 行定义的变量\""+ varImage + "\"的域成员在第"+treeNode.getBeginLine()+"行可能未初始化便进行了使用。");		
			return true;
			}
			break;
		case 1://初始化
			fsmInst.setFlag(true);
			for(UVF_PCheckInfo inited:initedVariable){
				if(varImage.equals(inited.getVariable().getImage()) && !inited.isInitedAsOne()){
					inited.setInitedAsOne(true);
					return false;
				}
			}
			initedVariable.add(new UVF_PCheckInfo(variable,true));
			return false;
		case 2://重新分配内存(包括：游离)
			return false;
		}
		//检测函数调用
		UVF_PInfo uvf_pInfo=checkMethod(vexNode.getTreenode(),variable);
		if(null != uvf_pInfo){
			addDomain(variable,uvf_pInfo.getInitedomain());
			IntegerDomain needInitedDomain=uvf_pInfo.getNeedInitedomain();
			if(!needInitedDomain.isEmpty()){
				//查看此区间是否已经被初始化
				for(UVF_PCheckInfo inited:initedVariable){
					//找到已经初始化的区间
					if(varImage.equals(inited.getVariable().getImage())){
						if(inited.isInitedAsOne() || inited.getInitedDomian().contains(needInitedDomain)){
							return false;
						}
					}
				}
				fsmInst.setRelatedASTNode(treeNode);
				fsmInst.setDesp("在第 " + variable.getNode().getBeginLine() + " 行定义的变量\""+ varImage + "\"的域成员在第"+treeNode.getBeginLine()+"行可能未初始化便进行了使用。");		
				return true;
			}
		}
		
		/**检测是否指针变量的域成员是否为使用*/
		String useXpath = ".//UnaryExpression/PostfixExpression[count(*)=2 and ./PrimaryExpression[(@Image='"+ varImage + "') and not(./Constant)] and not(./FieldId) and not(./ArgumentExpressionList) and (./Expression)]";
		List<SimpleNode> useList = StateMachineUtils.getEvaluationResults(treeNode, useXpath);
		Iterator<SimpleNode> useItr = useList.iterator();
		while (useItr.hasNext()) {
			ASTPostfixExpression checkNode = (ASTPostfixExpression) useItr.next();
			if (null == checkNode || (checkNode.getCurrentVexNode() != null && checkNode.getCurrentVexNode().getContradict()) || checkNode.jjtGetNumChildren()!=2 || !(checkNode.jjtGetChild(1) instanceof ASTExpression)) {
				continue;
			}
			//获取待检测与成员变量
			VariableNameDeclaration checkVariable=checkNode.getVariableDecl();
			if(null==checkVariable ||inited.contains(checkVariable)){//TODO 加上对可变下标的处理
				continue;
			}
			String checkVarImage=checkVariable.getImage();
			if(null==checkVarImage || checkVarImage.equals("")){
				continue;
			}
			//获取域敏感变量的下标的取值区间
			ASTExpression expressionNode=(ASTExpression)checkNode.jjtGetChild(1);
			if(expressionNode==null){
				continue;
			}
			ExpressionVistorData exprdata = new ExpressionVistorData();
			exprdata.currentvex=expressionNode.getCurrentVexNode();
			exprdata.sideeffect=true;
				
			ExpressionValueVisitor eVisitor=new ExpressionValueVisitor();
			exprdata=(ExpressionVistorData)eVisitor.visit((ASTAssignmentExpression)expressionNode.getFirstDirectChildOfType(ASTAssignmentExpression.class), exprdata);									
			Domain domain=exprdata.value.getDomain(exprdata.currentvex.getSymDomainset());
			//vDomain就是可变下标的可能取值范围
			IntegerDomain vDomain=Domain.castToIntegerDomain(domain);
			//查看此区间是否已经被初始化
			if(vDomain!=null){
				for(UVF_PCheckInfo inited:initedVariable){
					//找到已经初始化的区间
					if(varImage.equals(inited.getVariable().getImage())){
						if(inited.isInitedAsOne() || inited.getInitedDomian().contains(vDomain)){
							return false;
						}
					}
				}
			}
			//检测域成员变量是否初始化
			if (isInit(checkVariable, (SimpleNode) checkNode,treeNode)) {/**变量被初始化*/
				//增加域敏感变量的对应的区间
				addDomain(variable,vDomain);
				continue;
			}
			//检测域成员变量的使用
			/** p[0]&=0x03;类似这样的语句为地址分配，不视为未初始化使用 */
			if (checkNode.jjtGetParent().jjtGetParent().jjtGetParent().jjtGetNumChildren() > 1) {
				if (checkNode.jjtGetParent().jjtGetParent().jjtGetParent().jjtGetChild(1) instanceof ASTAssignmentOperator) {
					if (((ASTAssignmentOperator) (checkNode.jjtGetParent().jjtGetParent().jjtGetParent().jjtGetChild(1))).getOperators().equals("&=")) {
						continue;
					}
				}
			}
			SimpleNode parent = (SimpleNode) checkNode.getFirstParentOfType(ASTUnaryExpression.class);
			if(parent!=null&&parent.jjtGetParent() instanceof ASTUnaryExpression ){
				String opxpath = "./UnaryOperator[@Operators='&']";
				if(StateMachineUtils.getEvaluationResults((SimpleNode) parent.jjtGetParent(), opxpath)!=null)
					continue;
			}
			parent = checkNode;
			boolean flag=false;
			while (!(parent instanceof ASTStatement)) {
				parent = (SimpleNode)parent.jjtGetParent();
				/**避免形如sizeof(*a)这类误报*/
				if (parent instanceof ASTUnaryExpression && parent.getImage().equals("sizeof")) {
					flag=true;
					break;
				}
			}
			if(flag){
				continue;
			}
			/**对于**head节点，由于getTreenode()返回整个语句块，如果没有下面的检测，可能在语句块中先使用
			 * 后初始化的情况会漏报，所以要对语句块中变量使用出现及之前的statement节点进行初始化检测，如果变量
			 * 在这些语句中初始化，则跳转end状态，否则报告故障：未初始化使用。
			 */
			if(!(vexNode.getName().startsWith("for_head")||vexNode.getName().startsWith("if_head")
					||vexNode.getName().startsWith("while_head")||vexNode.getName().startsWith("do_while_head")
					||vexNode.getName().startsWith("switch_head")||vexNode.getName().startsWith("label_head_case"))
					&&(checkNode.getFirstParentOfType(ASTSelectionStatement.class)==null && checkNode.getFirstParentOfType(ASTIterationStatement.class)==null))
			{
				fsmInst.setRelatedASTNode(checkNode);
				fsmInst.setDesp("在第 " + variable.getNode().getBeginLine() + " 行定义的变量\""+ varImage + "\"的域成员变量\""+ checkVarImage + "\"在第"+checkNode.getBeginLine()+"行可能未初始化便进行了使用。");		
				return true;
			}
			else if(vexNode.getName().startsWith("while_head") ||vexNode.getName().startsWith("if_head")){
				parent = (SimpleNode) checkNode.jjtGetParent();
				while (parent != treeNode){
					parent = (SimpleNode) parent.jjtGetParent();
					if(treeNode.jjtGetChild(0) instanceof ASTExpression && parent == treeNode.jjtGetChild(0)){
						fsmInst.setRelatedASTNode(checkNode);
						fsmInst.setDesp("在第 " + variable.getNode().getBeginLine() + " 行定义的变量\""+ varImage + "\"的域成员变量\""+ checkVarImage + "\"在第"+checkNode.getBeginLine()+"行可能未初始化便进行了使用。");		
						return true;
					}
						
				}
				continue;
			}
			else if(!(vexNode.getName().startsWith("for_head")||vexNode.getName().startsWith("if_head")
					||vexNode.getName().startsWith("while_head")||vexNode.getName().startsWith("do_while_head")
					||vexNode.getName().startsWith("switch_head")||vexNode.getName().startsWith("label_head_case"))
					&&(checkNode.getFirstParentOfType(ASTSelectionStatement.class)!=null||checkNode.getFirstParentOfType(ASTIterationStatement.class)!=null)){
				treeNode = (SimpleNode) ((checkNode.getFirstParentOfType(ASTSelectionStatement.class)!=null)?checkNode.getFirstParentOfType(ASTSelectionStatement.class):checkNode.getFirstParentOfType(ASTIterationStatement.class));
				Node statementList=treeNode.getFirstChildOfType(ASTStatementList.class);
				Node end=checkNode.getFirstParentOfType(ASTStatement.class);
				if(statementList==null||statementList.jjtGetNumChildren()==0)
					{
					fsmInst.setRelatedASTNode(checkNode);
					fsmInst.setDesp("在第 " + variable.getNode().getBeginLine() + " 行定义的变量\""+ varImage + "\"的域成员变量\""+ checkVarImage + "\"在第"+checkNode.getBeginLine()+"行可能未初始化便进行了使用。");		
					return true;
					}
				else{
				for(int i=0;i!=statementList.jjtGetNumChildren();i++)
				{
					Node temp=statementList.jjtGetChild(i);
					if(temp == end ) 
						{
							fsmInst.setRelatedASTNode(checkNode);
							fsmInst.setDesp("在第 " + variable.getNode().getBeginLine() + " 行定义的变量\""+ varImage + "\"的域成员变量\""+ checkVarImage + "\"在第"+checkNode.getBeginLine()+"行可能未初始化便进行了使用。");		
							return true;
						}
				}
			}
			}
		}
		//如果已经对P[0]进行初始化，则不检测*p
		IntegerDomain vDomain=new IntegerDomain(0,0);
		//查看此区间是否已经被初始化
		for(UVF_PCheckInfo inited:initedVariable){
			//找到已经初始化的区间
			if(varImage.equals(inited.getVariable().getImage())){
				if(inited.isInitedAsOne() || inited.getInitedDomian().contains(vDomain)){
					return false;
				}
			}
		}
		//检测域成员变量*p
		useXpath=".//UnaryExpression[(./UnaryOperator[@Operators='*'])]/UnaryExpression/PostfixExpression[count(*)=1]/PrimaryExpression[@Image='"+varImage+"']";
		useList = StateMachineUtils.getEvaluationResults(treeNode, useXpath);
		useItr = useList.iterator();
		while (useItr.hasNext()) {
			ASTUnaryExpression unary=(ASTUnaryExpression) ((SimpleNode) useItr.next().getFirstParentOfType(ASTUnaryExpression.class)).getFirstParentOfType(ASTUnaryExpression.class);
			if (null == unary || (unary.getCurrentVexNode() != null && unary.getCurrentVexNode().getContradict())) {
				continue;
			}
			VariableNameDeclaration checkVariable = unary.getVariableDecl();
			if (isInitUnary(checkVariable, (SimpleNode) unary,treeNode)) {/**变量被初始化*/
				//增加域敏感变量的对应的区间
				addDomain(variable,vDomain);
				continue;
			}
			if(!(vexNode.getName().startsWith("for_head")||vexNode.getName().startsWith("if_head")
					||vexNode.getName().startsWith("while_head")||vexNode.getName().startsWith("do_while_head")
					||vexNode.getName().startsWith("switch_head")||vexNode.getName().startsWith("label_head_case"))
					&&(unary.getFirstParentOfType(ASTSelectionStatement.class)==null&& unary.getFirstParentOfType(ASTIterationStatement.class)==null))
			{
				SimpleNode parent = unary;
				while (!(parent instanceof ASTStatement)) {
					parent = (SimpleNode)parent.jjtGetParent();
					/**避免形如sizeof(*a)这类误报*/
					if (parent instanceof ASTUnaryExpression && parent.getImage().equals("sizeof")) {
						return false;
					}
				}
				fsmInst.setRelatedASTNode(unary);
				fsmInst.setDesp("在第 " + variable.getNode().getBeginLine() + " 行定义的变量\""+ variable.getImage() + "\"的成员变量"+unary.getImage()+"在第"+unary.getBeginLine()+"行可能未初始化便进行了使用。");		
				return true;
			}
		}
		return false;
	}
	private static boolean isInitUnary(VariableNameDeclaration varDecl,SimpleNode checkNode, SimpleNode treeNode) {
		/** step1 通过系统函数初始化 */
		/** step1.1: 通过函数sscanf( const char *, const char *, ...);进行初始化 */
		String ioInialXpath = ".//PostfixExpression[./PrimaryExpression[@Image='sscanf']]/ArgumentExpressionList/AssignmentExpression[last()]//PostfixExpression";
		List<SimpleNode> cinList = StateMachineUtils.getEvaluationResults(treeNode, ioInialXpath);
		for (SimpleNode tnode : cinList) {
			if (tnode.getCurrentVexNode() != null
					&& tnode.getCurrentVexNode().getContradict()) {
				continue;
			}
			if (checkNode.equals(tnode)) {
				return true;
			}
		}

		/**
		 * step1.2 先除掉strcpy(dest,src)中第二个元素不对其进行初始化；
		 * 同理strncpy(dest,src)不对其第二个元素进行初始化，当变量作为第二个参数传入时，返回false step1.3
		 * 同理，也应该除去strcmp(str1, str2)、strstr(str1, str2)，其中两个参数都应该初始化 step
		 * 1.4同理，应该除去fprintf(stream, "%s%c", s1, c ),其中应对以三个参数开始必须对其进行初始化
		 */
		/** step1.2 对于defaultFunList和cmpFuncList中的函数,变量位于特定形参的位置必须初始化过 */
		String defaultFunList[] = { "strcpy", "strncpy", "memcpy", "memmove",
				"strcat", "strncat" };
		String cmpFuncList[] = { "strstr", "strcmp", "strncmp", "memcmp" };
		String fprintfFuncList[] = { "fprintf", "wsprintf" };
		String ioNoInialxPath = ".//PostfixExpression[./ArgumentExpressionList[count(*)>=2]/AssignmentExpression/UnaryExpression[@Image='"
				+ varDecl.getImage() + "']]/PrimaryExpression";
		List<SimpleNode> funInialList = StateMachineUtils.getEvaluationResults(
				treeNode, ioNoInialxPath);
		for (SimpleNode idexp : funInialList) {
			ASTPrimaryExpression func = (ASTPrimaryExpression) idexp;
			SimpleNode expList = (SimpleNode) idexp.jjtGetParent().jjtGetChild(
					1);
			if (expList == null) {
				continue;
			}
			String funcName = func.getImage();
			for (String name : defaultFunList) {
				if (funcName.equals(name)) {
					/** 第二形参位置变量 */
					List<SimpleNode> list = StateMachineUtils
							.getEvaluationResults(expList,
									"./AssignmentExpression[last()]/UnaryExpression");
					if (list.size() > 0) {
						SimpleNode arg1 = list.get(0);
						if (arg1.getImage().equals(varDecl.getImage())) {
							return false;
						}
					}
				}
			}
			for (String name : cmpFuncList) {
				if (funcName.equals(name)) {
					List<SimpleNode> list = StateMachineUtils
							.getEvaluationResults(expList,
									"./AssignmentExpression/UnaryExpression");
					SimpleNode arg = list.get(0);
					/** 变量位于第一形参的位置 */
					if (arg.getImage().equals(varDecl.getImage())) {
						return false;
					}
					arg = list.get(1);
					/** 变量位于第二形参的位置 */
					if (arg.getImage().equals(varDecl.getImage())) {
						return false;
					}
				}
			}
			for (String name : fprintfFuncList) {
				if (funcName.equals(name)) {
					int expListChildNum = expList.jjtGetNumChildren();
					for (int j = 2; j < expListChildNum; j++) {
						SimpleNode arg = (SimpleNode) expList.jjtGetChild(j);
						if (arg.getImage().equals(varDecl.getImage())) {
							return false;
						}
					}
				}
			}
			return true;
		}
		/**
		 * step2.2: 通过函数调用进行初始化， 如果将变量传引用，则默认该变量由当前函数进行初始化, 声明void func(int &i,
		 * int b);当调用func(i, 0);时默认为对i进行了初始化(无传引用) step2.3: int * array;或者 int
		 * array[10];时,func(array, b);传入时，array为指针类型，视为func函数将其初始化
		 */
		String xPath = ".//PostfixExpression[./ArgumentExpressionList/AssignmentExpression//UnaryExpression[@Image='"
				+ varDecl.getImage() + "']]/PrimaryExpression";
		funInialList = StateMachineUtils.getEvaluationResults(treeNode, xPath);
		for (SimpleNode idexp : funInialList) {
			if (idexp.getCurrentVexNode() != null
					&& idexp.getCurrentVexNode().getContradict()) {
				continue;
			}
			/** 变量类型为数组或者指针时，视为对其初始化 */
			if (varDecl.getType() instanceof CType_AbstPointer) {
				return true;
			}
		}
		/**
		 * step3.1:但是针对AST的特殊语法void f(int &)定义，当调用f(i)时，算是给i进行赋值操作 //声明void
		 * func(int &i);传入参数的引用 //当调用func(i);时默认为对i进行了初始化(无) //zx: step3.2:
		 * 但是针对AST的特殊语法void f(int
		 * *)定义，当调用f(array)时，算是给array进行赋值操作[array为数组或指针类型]
		 */
		// 声明void func(int *array);
		// step4: “=”显示赋值的变量
		// 从第一判断位置转到最后，避免int i; i = i + 1;这种情况
		String assignInial = ".//AssignmentExpression[./AssignmentOperator[@Operators='= ' or @Operators='=']]";
		List<SimpleNode> assignNodeList = StateMachineUtils
				.getEvaluationResults(treeNode, assignInial);
		Iterator<SimpleNode> assignItr = assignNodeList.iterator();
		while (assignItr.hasNext()) {
			ASTAssignmentExpression assignNode = (ASTAssignmentExpression) assignItr
					.next();
			if (assignNode.getCurrentVexNode() != null
					&& assignNode.getCurrentVexNode().getContradict()) {
				continue;
			}
			/** 找到赋值表达式左边的那个变量 */
			String inialExpressionXpath = "./UnaryExpression[@Image='"+ varDecl.getImage() + "']";
			List<SimpleNode> inialExpList = StateMachineUtils
					.getEvaluationResults(assignNode, inialExpressionXpath);
			Iterator<SimpleNode> itr = inialExpList.iterator();
			while (itr.hasNext()) {
				SimpleNode idExp = itr.next();
				if (idExp.equals(checkNode)) {
					/** 判断‘=’右边是否也出现了同一个变量，如i = i + 1; */
					String sameVariableXpath = ".//UnaryExpression[@Image='"
							+ varDecl.getImage() + "']";
					List<SimpleNode> inialList = StateMachineUtils
							.getEvaluationResults(
									(SimpleNode) assignNode.jjtGetChild(2),
									sameVariableXpath);
					if (inialList != null && inialList.size() > 0) {
						/**
						 * 判断‘=’右边是否也出现了同一个变量，如array[1] = array[0] = 0;
						 * //添加判断，对”array[1] = array[0] = 0;“和”array[1] =
						 * array[0];“分别处理，后者视为未初始化使用
						 */
						String othervarxpath = ".//UnaryExpression[@Image!='"
								+ varDecl.getImage() + "' ]";
						List<SimpleNode> constantList = StateMachineUtils
								.getEvaluationResults(
										(SimpleNode) ((SimpleNode) inialList
												.get(0)).jjtGetParent()
												.jjtGetParent().jjtGetParent(),
										othervarxpath);
						if (constantList != null
								&& constantList.size() > inialList.size())
							return true;
						else {
							String funpath = ".//UnaryExpression[@Image='sizeof' and @Image='strlen']//UnaryExpression/PostfixExpression[not(./FieldId)]/PrimaryExpression[@Image='"
									+ varDecl.getImage() + "' and count(*)= 0]";
							List<SimpleNode> funList = StateMachineUtils
									.getEvaluationResults(
											(SimpleNode) assignNode
													.jjtGetChild(2), funpath);
							if (funList != null
									&& funList.size() >= inialList.size())
								return true;
							else
								return false;
						}
					}
					return true;
				}
			}
		}
		return false;
	}

//检查自定义函数调用点
public static UVF_PInfo checkMethod(SimpleNode simpleNode,VariableNameDeclaration variable) {
	if(simpleNode==null || variable==null){
		return null;
	}
	String varImage=variable.getImage();
	if(varImage==null || varImage.equals("")){
		return null;
	}
	String xpath=".//UnaryExpression/PostfixExpression[./ArgumentExpressionList//AssignmentExpression/UnaryExpression/PostfixExpression[count(*)=1]/PrimaryExpression[@Image='"+varImage+"']]/PrimaryExpression[@Method='true']";
	List<SimpleNode> list = StateMachineUtils.getEvaluationResults(simpleNode, xpath);
	int expNum=0;
	int paramIndex=0;
	List<SimpleNode> varList;
	for(SimpleNode snode:list){
		ASTPostfixExpression checkPost=(ASTPostfixExpression) snode.getFirstParentOfType(ASTPostfixExpression.class);
		if(checkPost==null || checkPost.jjtGetNumChildren()<2){
			continue;
		}
		ASTArgumentExpressionList expList=(ASTArgumentExpressionList) checkPost.getFirstChildOfType(ASTArgumentExpressionList.class);
		if(expList==null || expList.jjtGetNumChildren()==0){
			continue;
		}
		expNum=expList.jjtGetNumChildren();
		for(int i=0;i<expNum;i++){
			SimpleNode checkParam=(SimpleNode) expList.jjtGetChild(i);
			if(checkParam==null || checkParam.jjtGetNumChildren()==0){
				continue;
			}
			varList=StateMachineUtils.getEvaluationResults(checkParam, "./UnaryExpression/PostfixExpression[count(*)=1]/PrimaryExpression[@Image='"+varImage+"']");
			if(varList!=null && varList.size()>0){
					paramIndex=i;
					break;
			}
			paramIndex=-1;
		}
		if(paramIndex==-1){
			continue;
		}
		MethodNameDeclaration methodDecl = StateMachineUtils.getMethodNameDeclaration(snode);
		if(methodDecl == null || methodDecl.getMethodSummary() == null)
			 continue; 
		//如果该函数有关于指针变量UVF_P前置信息 
		MethodUVF_PPreCondition uvf_pfeature = (MethodUVF_PPreCondition)methodDecl.getMethodSummary().findMethodFeature(MethodUVF_PPreCondition.class); 
		if (uvf_pfeature == null) 
			continue;
		Set<VariableNameDeclaration> variables = uvf_pfeature.getUVF_PVariables(); 
		for(VariableNameDeclaration var1 : variables) {
			UVF_PInfo uvf_pInfo = uvf_pfeature.getUVF_PInfo(var1);
			if(paramIndex==uvf_pInfo.getParamIndex()) {
				return uvf_pInfo;
			}
		}
	}
	//ff(&a);
	xpath=".//UnaryExpression/PostfixExpression[./ArgumentExpressionList//AssignmentExpression/UnaryExpression[./UnaryOperator[@Operators='&']]/UnaryExpression/PostfixExpression[count(*)=1]/PrimaryExpression[@Image='"+varImage+"']]/PrimaryExpression";
	list = StateMachineUtils.getEvaluationResults(simpleNode, xpath);
	if(list!=null && list.size()>0){
		return new UVF_PInfo(variable.getImage(), -10, UVF_PType.NOT_NEED,IntegerDomain.getEmptyDomain(),IntegerDomain.getFullDomain());
	}
		return null;
	}

/**
 * 将域敏感变量的域区间进行合并
 * @param variable
 * @param vDomain
 * @return true|false
 */
private static boolean addDomain(VariableNameDeclaration variable,IntegerDomain vDomain) {
	if(null==variable || null==vDomain){
		return false;
	}
	String varImage=variable.getImage();
	for(UVF_PCheckInfo inited:initedVariable){
		//找到已经初始化的区间
		if(varImage.equals(inited.getVariable().getImage())){
			if(inited.isInitedAsOne() ||inited.getInitedDomian().contains(vDomain)){
				return true;
			}
			inited.getInitedDomian().mergeWith(vDomain.jointoOneInterval());
			return true;
		}
	}
	//没有找到已经初始化的区间
	initedVariable.add(new UVF_PCheckInfo(variable,vDomain));
	return true;
}
	/** 检测与成员变量是否被初始化 */
	public static boolean isInit(VariableNameDeclaration varDecl,SimpleNode checkNode, SimpleNode treeNode) {
		/** step1 通过系统函数初始化 */
		/** step1.1: 通过函数sscanf( const char *, const char *, ...);进行初始化 */
		String ioInialXpath = ".//PostfixExpression[./PrimaryExpression[@Image='sscanf']]/ArgumentExpressionList/AssignmentExpression[last()]//PostfixExpression";
		List<SimpleNode> cinList = StateMachineUtils.getEvaluationResults(treeNode, ioInialXpath);
		for (SimpleNode tnode : cinList) {
			if (tnode.getCurrentVexNode() != null
					&& tnode.getCurrentVexNode().getContradict()) {
				continue;
			}
			if (checkNode.equals(tnode)) {
				return true;
			}
		}

		/**
		 * step1.2 先除掉strcpy(dest,src)中第二个元素不对其进行初始化；
		 * 同理strncpy(dest,src)不对其第二个元素进行初始化，当变量作为第二个参数传入时，返回false step1.3
		 * 同理，也应该除去strcmp(str1, str2)、strstr(str1, str2)，其中两个参数都应该初始化 step
		 * 1.4同理，应该除去fprintf(stream, "%s%c", s1, c ),其中应对以三个参数开始必须对其进行初始化
		 */
		/** step1.2 对于defaultFunList和cmpFuncList中的函数,变量位于特定形参的位置必须初始化过 */
		String defaultFunList[] = { "strcpy", "strncpy", "memcpy", "memmove",
				"strcat", "strncat" };
		String cmpFuncList[] = { "strstr", "strcmp", "strncmp", "memcmp" };
		String fprintfFuncList[] = { "fprintf", "wsprintf" };
		String ioNoInialxPath = ".//PostfixExpression[./ArgumentExpressionList[count(*)>=2]/AssignmentExpression/UnaryExpression/PostfixExpression[@Image='"
				+ varDecl.getImage() + "']]/PrimaryExpression";
		List<SimpleNode> funInialList = StateMachineUtils.getEvaluationResults(
				treeNode, ioNoInialxPath);
		for (SimpleNode idexp : funInialList) {
			ASTPrimaryExpression func = (ASTPrimaryExpression) idexp;
			SimpleNode expList = (SimpleNode) idexp.jjtGetParent().jjtGetChild(
					1);
			if (expList == null) {
				continue;
			}
			String funcName = func.getImage();
			for (String name : defaultFunList) {
				if (funcName.equals(name)) {
					/** 第二形参位置变量 */
					List<SimpleNode> list = StateMachineUtils
							.getEvaluationResults(expList,
									"./AssignmentExpression[last()]/UnaryExpression/PostfixExpression");
					if (list.size() > 0) {
						SimpleNode arg1 = list.get(0);
						if (arg1.getImage().equals(varDecl.getImage())) {
							return false;
						}
					}
				}
			}
			for (String name : cmpFuncList) {
				if (funcName.equals(name)) {
					List<SimpleNode> list = StateMachineUtils
							.getEvaluationResults(expList,
									"./AssignmentExpression/UnaryExpression/PostfixExpression");
					SimpleNode arg = list.get(0);
					/** 变量位于第一形参的位置 */
					if (arg.getImage().equals(varDecl.getImage())) {
						return false;
					}
					arg = list.get(1);
					/** 变量位于第二形参的位置 */
					if (arg.getImage().equals(varDecl.getImage())) {
						return false;
					}
				}
			}
			for (String name : fprintfFuncList) {
				if (funcName.equals(name)) {
					int expListChildNum = expList.jjtGetNumChildren();
					for (int j = 2; j < expListChildNum; j++) {
						SimpleNode arg = (SimpleNode) expList.jjtGetChild(j);
						if (arg.getImage().equals(varDecl.getImage())) {
							return false;
						}
					}
				}
			}
			return true;
		}
		/**
		 * step2.1: 通过函数调用进行初始化，如果将变量取地址做参数传入函数中，则默认该变量由当前函数进行初始化 形如: func(&a);
		 * scanf("%d", &a); func(&a, 1);两者语法树稍有不同，C++特定的语法造成(此处语法无区别)
		 */
		String xPath = ".//PostfixExpression[./PrimaryExpression]/ArgumentExpressionList/AssignmentExpression/UnaryExpression[./UnaryOperator[@Operators='&']]/UnaryExpression/PostfixExpression";
		xPath += " | .//PostfixExpression[./PrimaryExpression]/ArgumentExpressionList/AssignmentExpression/CastExpression[./TypeName]/UnaryExpression[./UnaryOperator[@Operators='&']]/UnaryExpression/PostfixExpression";
		funInialList = StateMachineUtils.getEvaluationResults(treeNode, xPath);
		for (SimpleNode idExp : funInialList) {
			if (idExp.getCurrentVexNode() != null
					&& idExp.getCurrentVexNode().getContradict()) {
				continue;
			}
			if (idExp.equals(checkNode)) {
				return true;
			}
		}
		/**
		 * step2.2: 通过函数调用进行初始化， 如果将变量传引用，则默认该变量由当前函数进行初始化, 声明void func(int &i,
		 * int b);当调用func(i, 0);时默认为对i进行了初始化(无传引用) step2.3: int * array;或者 int
		 * array[10];时,func(array, b);传入时，array为指针类型，视为func函数将其初始化
		 */
		xPath = ".//PostfixExpression[./ArgumentExpressionList/AssignmentExpression//UnaryExpression/PostfixExpression[@Image='"
				+ varDecl.getImage() + "']]/PrimaryExpression";
		funInialList = StateMachineUtils.getEvaluationResults(treeNode, xPath);
		for (SimpleNode idexp : funInialList) {
			if (idexp.getCurrentVexNode() != null
					&& idexp.getCurrentVexNode().getContradict()) {
				continue;
			}
			/** 变量类型为数组或者指针时，视为对其初始化 */
			if (varDecl.getType() instanceof CType_AbstPointer) {
				return true;
			}
		}
		/**
		 * step3.1:但是针对AST的特殊语法void f(int &)定义，当调用f(i)时，算是给i进行赋值操作 //声明void
		 * func(int &i);传入参数的引用 //当调用func(i);时默认为对i进行了初始化(无) //zx: step3.2:
		 * 但是针对AST的特殊语法void f(int
		 * *)定义，当调用f(array)时，算是给array进行赋值操作[array为数组或指针类型]
		 */
		// 声明void func(int *array);
		// step4: “=”显示赋值的变量
		// 从第一判断位置转到最后，避免int i; i = i + 1;这种情况
		String assignInial = ".//AssignmentExpression[./AssignmentOperator[@Operators='= ' or @Operators='=']]";
		List<SimpleNode> assignNodeList = StateMachineUtils
				.getEvaluationResults(treeNode, assignInial);
		Iterator<SimpleNode> assignItr = assignNodeList.iterator();
		while (assignItr.hasNext()) {
			ASTAssignmentExpression assignNode = (ASTAssignmentExpression) assignItr
					.next();
			if (assignNode.getCurrentVexNode() != null
					&& assignNode.getCurrentVexNode().getContradict()) {
				continue;
			}
			/** 找到赋值表达式左边的那个变量 */
			String inialExpressionXpath = "./UnaryExpression/PostfixExpression[@Image='"+ varDecl.getImage() + "']";
			List<SimpleNode> inialExpList = StateMachineUtils
					.getEvaluationResults(assignNode, inialExpressionXpath);
			Iterator<SimpleNode> itr = inialExpList.iterator();
			while (itr.hasNext()) {
				SimpleNode idExp = itr.next();
				if (idExp.equals(checkNode)) {
					/** 判断‘=’右边是否也出现了同一个变量，如i = i + 1; */
					String sameVariableXpath = ".//UnaryExpression/PostfixExpression[@Image='"
							+ varDecl.getImage() + "']";
					List<SimpleNode> inialList = StateMachineUtils
							.getEvaluationResults(
									(SimpleNode) assignNode.jjtGetChild(2),
									sameVariableXpath);
					if (inialList != null && inialList.size() > 0) {
						/**
						 * 判断‘=’右边是否也出现了同一个变量，如array[1] = array[0] = 0;
						 * //添加判断，对”array[1] = array[0] = 0;“和”array[1] =
						 * array[0];“分别处理，后者视为未初始化使用
						 */
						String othervarxpath = ".//UnaryExpression/PostfixExpression[@Image!='"
								+ varDecl.getImage() + "' ]";
						List<SimpleNode> constantList = StateMachineUtils
								.getEvaluationResults(
										(SimpleNode) ((SimpleNode) inialList
												.get(0)).jjtGetParent()
												.jjtGetParent().jjtGetParent(),
										othervarxpath);
						if (constantList != null
								&& constantList.size() > inialList.size())
							return true;
						else {
							String funpath = ".//UnaryExpression[@Image='sizeof' and @Image='strlen']//UnaryExpression/PostfixExpression[not(./FieldId)]/PrimaryExpression[@Image='"
									+ varDecl.getImage() + "' and count(*)= 0]";
							List<SimpleNode> funList = StateMachineUtils
									.getEvaluationResults(
											(SimpleNode) assignNode
													.jjtGetChild(2), funpath);
							if (funList != null
									&& funList.size() >= inialList.size())
								return true;
							else
								return false;
						}
					}
					return true;
				}
			}
		}
		return false;
	}
}
class UVF_PCheckInfo{
	/**已经被初始化的区间*/
	private IntegerDomain initedDomian;
	/**指针变量*/
	private VariableNameDeclaration variable;
	/**指针变量是否被整体初始化*/
	private boolean initedAsOne;
	
	public UVF_PCheckInfo(VariableNameDeclaration variable){
		initedDomian=new IntegerDomain();
		this.variable=variable;
		initedAsOne=false;
	}
	public UVF_PCheckInfo(VariableNameDeclaration variable,boolean initedAsOne){
		initedDomian=new IntegerDomain();
		this.variable=variable;
		this.initedAsOne=initedAsOne;
	}
	public UVF_PCheckInfo(VariableNameDeclaration variable,IntegerDomain domain){
		initedDomian=domain;
		this.variable=variable;
		this.initedAsOne=false;
	}
	public IntegerDomain getInitedDomian() {
		return initedDomian;
	}
	public void setInitedDomian(IntegerDomain initedDomian) {
		this.initedDomian = initedDomian;
	}
	public VariableNameDeclaration getVariable() {
		return variable;
	}
	public void setVariable(VariableNameDeclaration variable) {
		this.variable = variable;
	}
	public boolean isInitedAsOne() {
		return initedAsOne;
	}
	public void setInitedAsOne(boolean initedAsOne) {
		this.initedAsOne = initedAsOne;
	}
}
