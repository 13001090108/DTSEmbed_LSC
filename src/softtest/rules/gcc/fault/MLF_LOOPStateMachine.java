package softtest.rules.gcc.fault;


import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.ASTArgumentExpressionList;
import softtest.ast.c.ASTIterationStatement;
import softtest.ast.c.Node;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.Edge;
import softtest.cfg.c.VexNode;
import softtest.config.c.Config;
import softtest.domain.c.interval.PointerDomain;
import softtest.domain.c.interval.PointerValue;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.ScopeType;
import softtest.interpro.c.Variable;
import softtest.rules.c.AliasSet;
import softtest.rules.c.BasicStateMachine;
import softtest.rules.c.StateMachineUtils;
import softtest.summary.c.MMFetureType;
import softtest.summary.gcc.fault.MethodMMFeature;
import softtest.summary.gcc.fault.MethodMMFeatureVisitor;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.MethodScope;
import softtest.symboltable.c.Scope;
import softtest.symboltable.c.Search;
import softtest.symboltable.c.SourceFileScope;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.Type.CType;
import softtest.symboltable.c.Type.CType_Pointer;

public class MLF_LOOPStateMachine extends BasicStateMachine {
	enum CheckType
	{
		C_FREE_OK, C_FREE_ERROR, ALL_ERROR
	};
	
	public void registFetureVisitors()
	{
		super.registFetureVisitors();
		InterContext.addSideEffectVisitor(MethodMMFeatureVisitor.getInstance());
	}
	
	public final static String[] CALLOC_FUNCS = { "calloc", "malloc", "alloc",
		"strdup", "realloc" };
	
	public static List<FSMMachineInstance> createMLF_LOOPStateMachines(SimpleNode node, FSMMachine fsm)
	{
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		String xPath = ".//Statement/IterationStatement//CompoundStatement";//查找所有循环的循环体
        List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
        List<SimpleNode> evaluationResultstemp = StateMachineUtils.getEvaluationResults(node, xPath);
        
        String xPath1 = ".//UnaryExpression/PostfixExpression/PrimaryExpression[@Method='true']";
        for (SimpleNode tnode : evaluationResultstemp) {
        	List<SimpleNode> evaluationResults1 = StateMachineUtils.getEvaluationResults(tnode, xPath1);
        	for(SimpleNode tnode1 : evaluationResults1){
        		if(!evaluationResults.contains(tnode1)){
        			evaluationResults.add(tnode1);
        		}
        	}
        }
        HashSet<VariableNameDeclaration> reoccrs = new HashSet<VariableNameDeclaration>();
        for (SimpleNode snode : evaluationResults)
		{
        	MethodNameDeclaration methodDecl = StateMachineUtils
			.getMethodNameDeclaration(snode);
			if (methodDecl == null ||methodDecl.getImage() == null)
			{
				continue;
			}
			VariableNameDeclaration varDecl = null;
	
			// C语言库中的申请内存的函数
			if (isCAllocFunc(methodDecl.getImage()))		
			{		
				varDecl = MethodMMFeatureVisitor.findAssginDeclInQual(snode);
				if (varDecl != null)
				{
					addFSM(methodDecl.getImage(), reoccrs, list, varDecl,MMFetureType.MALLOC, snode, fsm);
				}
	
				continue;
			}
			if (methodDecl.getMethodSummary() == null)
			{
				continue;
			}
			MethodMMFeature mmFeture = (MethodMMFeature) methodDecl
					.getMethodSummary()
					.findMethodFeature(MethodMMFeature.class);
			if (mmFeture == null)
			{
				continue;
			}
	
			// 检查是否通过返回值返回申请内存指针
			FSMMachineInstance fsmins = null;
			if (mmFeture.isAllocateAndReturn())
			{		
				varDecl = MethodMMFeatureVisitor.findAssginDeclInQual(snode);
				if (varDecl != null)
				{
					fsmins = addFSM(methodDecl.getImage(), reoccrs, list,
							varDecl,MMFetureType.MALLOC, snode, fsm);
				}
	
				
				if (fsmins != null)
				{
					fsmins.setTraceinfo(mmFeture.getRetTrace());
				}
			}
			// 检查是否通过参数返回MM相关变量
			HashMap<Variable, MMFetureType> mmFetures = mmFeture.getMMFetures();
			for (Variable variable : mmFetures.keySet())
			{
				//???wavericq
				if (variable.isParam() && variable.getType() instanceof CType_Pointer && CType.getOrignType(variable.getType()) instanceof CType_Pointer)
				{
					Node n = snode.getNextSibling();
					if (n != null && n instanceof ASTArgumentExpressionList)
					{
						varDecl = MethodMMFeatureVisitor.getArgDecl(
								(ASTArgumentExpressionList) n, variable
										.getParamIndex());
					}						
					if (varDecl != null)
					{
						MMFetureType type = mmFetures.get(variable);
						if (type == MMFetureType.MALLOC)
						{
							fsmins = addFSM(methodDecl.getImage(), reoccrs,
									list, varDecl, type, snode, fsm);
							if (fsmins != null)
							{
								fsmins.setTraceinfo(mmFeture.getDesp(variable));
							}
						}
					}
				}
				//目前只有过程间和过程内两种检查，不应该只针对局部变量,这里对全局变量特殊处理
				else if(variable.getScopeType() == ScopeType.INTER_SCOPE ){
					SourceFileScope sfScope = findSourceFileScope(snode.getScope());
					VariableNameDeclaration varDecl1 = (VariableNameDeclaration)Search.searchInVariableAndMethodUpward(variable.getName(), sfScope);
					MMFetureType type = mmFetures.get(variable);
					if (type == MMFetureType.MALLOC)
					{
						fsmins = addFSM(methodDecl.getImage(), reoccrs,
								list, varDecl1, type, snode, fsm);
						if (fsmins != null)
						{
							fsmins.setTraceinfo(mmFeture.getDesp(variable));
						}
					}
				}				
			}
		}
		return list;
	}
	
	private static SourceFileScope findSourceFileScope(Scope scope)
	{
		Scope parent = scope;
		
		while(parent!=null && !(parent instanceof SourceFileScope))
		{
			parent = parent.getParent();
		}
		
		return (SourceFileScope)parent;
	}
	/**
	 * 判断莫函数是否是C语言中申请内存的库函数
	 * 
	 * @param funcName
	 * @return
	 */
	
	private static boolean isCAllocFunc(String funcName)
	{
		if (funcName == null)
		{
			return false;
		}
		for (int i = 0; i < CALLOC_FUNCS.length; i++)
		{
			if (CALLOC_FUNCS[i].equals(funcName))
			{
				return true;
			}
		}
		return false;
	}
	
	private static FSMMachineInstance addFSM(String methodName,
			HashSet<VariableNameDeclaration> reoccur,
			List<FSMMachineInstance> list, VariableNameDeclaration varDecl,
			MMFetureType type, SimpleNode node, FSMMachine fsm)
	{

		if (!reoccur.contains(varDecl) && !(varDecl.isParam() || varDecl.getScope()instanceof MethodScope)
				&& (varDecl.getType() instanceof CType_Pointer || CType.getOrignType(varDecl.getType()) instanceof CType_Pointer))
		{
			FSMMachineInstance fsminstance = fsm.creatInstance();
			AliasSet alias = new AliasSet();
			
			fsminstance.setResultString(varDecl.getImage());

			alias.setResouceName("Memory");
			alias.setforLoop(true);

			fsminstance.setRelatedObject(alias);
			fsminstance.setStateData(type);
			fsminstance.setRelatedASTNode(node);
			
			SimpleNode loopNode = (SimpleNode) node.getFirstParentOfType(ASTIterationStatement.class);
			fsminstance.setNodeUseToFindPosition(loopNode);
			String desp = "";
			if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH)
			{
				desp = "The varibale \"" + varDecl.getImage()
						+ "\" which defines in line "
						+ varDecl.getNode().getBeginLine()
						+ " is allocated memory in line " + node.getBeginLine();
				if (methodName != null)
				{
					desp += " by \"" + methodName + "\"";
				}
			}
			else
				if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
				{
					desp = "在第 " + varDecl.getNode().getBeginLine()
							+ " 行定义的变量 \"" + varDecl.getImage() + "\"在 "
							+ node.getBeginLine() + "行";
					if (methodName != null)
					{
						desp += " 使用方法 \"" + methodName + "\"分配了内存";
					}

				}
			fsminstance.setDesp(desp);
			fsminstance.setRelatedVariable(varDecl);
			list.add(fsminstance);
			reoccur.add(varDecl);
			

			return fsminstance;
		}
		return null;
	}
	
	public static boolean checkLoop(VexNode vex, FSMMachineInstance fsmin) {
    	List<Edge> list = new ArrayList<Edge>();
		for (Enumeration<Edge> e = vex.getInedges().elements(); e.hasMoreElements();) {
			list.add(e.nextElement());
		}
    	if(list.size()==1){
    		Edge inedge = list.iterator().next();
    		if(inedge.getName().startsWith("T")){
    		    VexNode preVex = inedge.getTailNode();
    	        if(preVex.getName().startsWith("for_head")||preVex.getName().startsWith("while_head")||preVex.getName().startsWith("doWhile_out"))
    		        if(preVex.getTreenode() == fsmin.getNodeUseToFindPosition())
    	        	    return true;
    		}
    	}
    	return false;
    }
	
	public static boolean checkLoopEnd(VexNode vex, FSMMachineInstance fsmin){
    	List<Edge> list = new ArrayList<Edge>();
		for (Enumeration<Edge> e = vex.getInedges().elements(); e.hasMoreElements();) {
			list.add(e.nextElement());
		}
    	if(list.size()==1){
    		Edge inedge = list.iterator().next();
    		VexNode preVex = inedge.getTailNode();
    	    if(preVex.getName().startsWith("for_out")||preVex.getName().startsWith("while_out")||preVex.getName().startsWith("doWhile_finalOut"))
    		    return true;
    	}
    	return false;
    }
	
	public static boolean checkCAllocMethod(List nodes, FSMMachineInstance fsmin)
	{
		Iterator i = nodes.iterator();
		while (i.hasNext())
		{
			Object o = i.next();
			if (fsmin.getRelatedASTNode() == o)
			{
					if (fsmin.getStateData() == MMFetureType.MALLOC)
					{
						AliasSet alias = (AliasSet) fsmin.getRelatedObject();
						alias.add(fsmin.getRelatedVariable());
						return true;
					}
			}
		}
		return false;
	}

	public static boolean checkFreeOrDelete(List nodes, FSMMachineInstance fsmin)
	{
		if (isValidMethod(nodes, fsmin, CheckType.ALL_ERROR))
		{
			if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH)
			{
				fsmin.setDesp(fsmin.getDesp() + ", is double freed");
			}
			else
				if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
				{
					fsmin.setDesp(fsmin.getDesp() + "，在第"+((SimpleNode)nodes.get(0)).getEndLine()+"行被释放了两次");
				}
			return true;
		}
		return false;
	}

	public static boolean checkCFreeMethod(List nodes, FSMMachineInstance fsmin)
	{
		return isValidMethod(nodes, fsmin, CheckType.C_FREE_OK);
	}

	public static boolean checkCFreeMethodError(List nodes,
			FSMMachineInstance fsmin)
	{
		if (isValidMethod(nodes, fsmin, CheckType.C_FREE_ERROR))
		{
			if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH)
			{
				fsmin.setDesp(fsmin.getDesp() + ", is deallocated improperly");
			}
			else
				if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
				{
					fsmin.setDesp(fsmin.getDesp() + ", 没有被恰当的释放");
				}
			return true;
		}
		return false;
	}

    /**xwt 解决重复分配的问题。目前认为：在分配状态如果遇到再分配，且别名集中元素唯一，则进入error状态*/  
	public static boolean checkAllocOrNewError(List nodes, FSMMachineInstance fsmin){
		boolean returnTrue = false;
		for (Object o : nodes){
			SimpleNode snode = ((SimpleNode)o);
			MethodNameDeclaration methodDecl = StateMachineUtils.getMethodNameDeclaration(snode);
	        if (methodDecl == null)
                continue;
			VariableNameDeclaration varDecl = null;		
			// C语言库中的申请内存的函数
			if (isCAllocFunc(methodDecl.getImage()))		
			{		
				varDecl = MethodMMFeatureVisitor.findAssginDeclInQual(snode);
				if (varDecl != null){
					AliasSet set  = (AliasSet) fsmin.getRelatedObject();
                    if(varDecl == fsmin.getRelatedVariable() && set.getTable().size() == 1)
                    	returnTrue = true;
				}
			}
			if (methodDecl.getMethodSummary() == null)
				continue;
			MethodMMFeature mmFeture = (MethodMMFeature) methodDecl.getMethodSummary().findMethodFeature(MethodMMFeature.class);
			if (mmFeture == null)
				continue;
			// 检查是否通过返回值返回申请内存指针
			FSMMachineInstance fsmins = null;
			if (mmFeture.isAllocateAndReturn())
			{
				varDecl = MethodMMFeatureVisitor.findAssginDeclInQual(snode);
				if (varDecl != null)
				{
					AliasSet set  = (AliasSet) fsmin.getRelatedObject();
                    if(varDecl == fsmin.getRelatedVariable() && set.getTable().size() == 1)
                    	returnTrue= true;
				}			
			}
			// 检查是否通过参数返回MM相关变量
			HashMap<Variable, MMFetureType> mmFetures = mmFeture.getMMFetures();
			for (Variable variable : mmFetures.keySet())
			{
				if (variable.isParam() && variable.getType() instanceof CType_Pointer && CType.getOrignType(variable.getType()) instanceof CType_Pointer)
				{
					Node n = snode.getNextSibling();
					if (n != null && n instanceof ASTArgumentExpressionList)
					{
						varDecl = MethodMMFeatureVisitor.getArgDecl(
								(ASTArgumentExpressionList) n, variable
										.getParamIndex());
					}					
					if (varDecl != null)
					{
						MMFetureType type = mmFetures.get(variable);
						if (type == MMFetureType.MALLOC)
						{
							AliasSet set  = (AliasSet) fsmin.getRelatedObject();
		                    if(varDecl == fsmin.getRelatedVariable() && set.getTable().size() == 1)
		                    	returnTrue= true;
						}
					}
				}
				//目前只有过程间和过程内两种检查，不应该只针对局部变量,这里对全局变量特殊处理
				else if(variable.getScopeType() == ScopeType.INTER_SCOPE ){
					SourceFileScope sfScope = findSourceFileScope(snode.getScope());
					VariableNameDeclaration varDecl1 = (VariableNameDeclaration)Search.searchInVariableAndMethodUpward(variable.getName(), sfScope);
					MMFetureType type = mmFetures.get(variable);
					if (type == MMFetureType.MALLOC)
					{
						AliasSet set  = (AliasSet) fsmin.getRelatedObject();
	                    if(varDecl == fsmin.getRelatedVariable() && set.getTable().size() == 1)
	                    	returnTrue = true;
					}
				}
				if(returnTrue == true){
					fsmin.setDesp(fsmin.getDesp() + "，在第"+snode.getEndLine()+"行重复分配内存会造成内存泄漏");
				}
			}
		}
		return false;	
	}
	
	
	public static boolean isValidMethod(List nodes, FSMMachineInstance fsmin,CheckType checkType)
	{
		Iterator i = nodes.iterator();
		AliasSet alias = (AliasSet) fsmin.getRelatedObject();
		while (i.hasNext())
		{
			SimpleNode node = (SimpleNode) i.next();
			MethodNameDeclaration methodDecl = StateMachineUtils
					.getMethodNameDeclaration(node);
			if (methodDecl == null)
			{
				continue;
			}
			VariableNameDeclaration varDecl = null;
			if (methodDecl.getImage().equals("free"))
			{

				varDecl = MethodMMFeatureVisitor.findArgDeclInQual(node);

				
				if (varDecl != null && alias.getTable().contains(varDecl))
				{
					if (checkType == CheckType.C_FREE_OK)
					{
						return true;
					}
					else
						if (checkType == CheckType.ALL_ERROR)
						{
							return true;
						}
				}
			}
			if (methodDecl.getMethodSummary() == null)
			{
				continue;
			}
			MethodMMFeature mmFeture = (MethodMMFeature) methodDecl
					.getMethodSummary()
					.findMethodFeature(MethodMMFeature.class);
			if (mmFeture == null)
			{
				continue;
			}
			HashMap<Variable, MMFetureType> mmFetures = mmFeture.getMMFetures();

			for (Variable variable : mmFetures.keySet())
			{
				if (variable.isParam())
				{
					Node n = node.getNextSibling();
					if (n != null && n instanceof ASTArgumentExpressionList)
					{
						varDecl = MethodMMFeatureVisitor.getArgDecl(
								(ASTArgumentExpressionList) n, variable
										.getParamIndex());
					}

					if (varDecl != null && alias.getTable().contains(varDecl))
					{
						boolean comp = false;
						boolean isCpp = false;
						MMFetureType type = mmFetures.get(variable);
						if ( type != MMFetureType.FREE)
						{
							return false;
						}
						if (checkType == CheckType.ALL_ERROR)
						{
							return true;
						}
						else
							if (type == MMFetureType.FREE
										&& fsmin.getStateData() == MMFetureType.MALLOC)
							{
								comp = true;
							}
						if (checkType == CheckType.C_FREE_ERROR && isCpp)
						{
							return true;
						}
						else
							if (checkType == CheckType.C_FREE_OK && !isCpp
									&& comp)
							{
								return true;
							}
					}
				}
			}

		}
		return false;
	}

	public static boolean checkMemoryLeak(VexNode vex, FSMMachineInstance fsmin)
	{
		AliasSet alias = (AliasSet) fsmin.getRelatedObject();
		if (alias.getHasReturned())
		{
			return false;
		}
		// 特殊处理指针分配失败出口处，避免误报
		if (isNullPoint(vex, fsmin.getRelatedVariable())
				&& vex.getName().startsWith("return"))
		{
			return false;
		}
		if (!alias.isEmpty())
		{
			return false;
		}
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH)
		{
			fsmin.setDesp(fsmin.getDesp() + ", may lead to memory leak");
		}
		else
			if (Config.DTS_LANGUAGE == Config.LANG_CHINESE)
			{
				fsmin.setDesp(fsmin.getDesp() + "，在第"+vex.getTreenode().getEndLine()+"行会造成内存泄漏");
			}
		return true;
	}

	public static boolean checkDomain(VexNode vex, FSMMachineInstance fsmin)
	{
		AliasSet alias = (AliasSet) fsmin.getRelatedObject();
		for (Enumeration<VariableNameDeclaration> e = alias.getTable()
				.elements(); e.hasMoreElements();)
		{
			VariableNameDeclaration v = e.nextElement();
			boolean isifout = false;
			if (vex.getInedges().size() == 1)
			{
				Edge edge = vex.getInedges().elements().nextElement();
				if (edge.getTailNode().getName().startsWith("if_head"))
				{
					isifout = true;
				}
			}
			if (!isifout)
			{
				if (isNullPoint(vex, v))
				{
					return true;
				}
			}
			else
			{
				// DomainSet lastDomainSet = vex.getLastDomainSet();
				if (isNullPoint(vex, v))
				{
					return true;
				}
			}
		}
		// 特殊处理指针分配失败出口处，避免误报
		if (vex.getName().startsWith("return"))
		{
			VariableNameDeclaration v = fsmin.getRelatedVariable();
			if (vex.getDomain(v) instanceof PointerDomain)
			// && !((PointerDomain) vex.getDomain(v)).isUnknown())
			{
				PointerDomain domain = (PointerDomain) vex.getDomain(v);
				// if (domain.range.isCanonical() && domain.range.isIn(0)) //？？？
				if (domain.getValue() == PointerValue.NULL)
				{
					return true;
				}
			}
		}
		return false;
	}

	// 是不是要修改为lastdomainset————wavericq
	private static boolean isNullPoint(VexNode vexNode,VariableNameDeclaration v)
	{

		if (vexNode.getDomain(v) instanceof PointerDomain)
		// && !((PointerDomain) vexNode.getDomain(v)).isUnknown())
		{
			PointerDomain domain = (PointerDomain) vexNode.getDomain(v);
			//if (domain.range.isCanonical() && domain.range.isIn(0))
			if (domain.getValue() == PointerValue.NULL)
			{
				return true;
			}
		}
		return false;
	}
	
	public static boolean isNullPoint(VexNode vexNode,boolean last, VariableNameDeclaration v)
	{
		
		vexNode.setfsmCompute(last);
		if(vexNode.getDomain(v) instanceof PointerDomain)                 //有问题
		{
			PointerDomain domain = (PointerDomain) vexNode.getDomain(v);
			if (domain.getValue() == PointerValue.NULL)                          //有问题
			{
				return true;
			}
		}
		
		vexNode.setfsmCompute(false);                            //???
		return false;
	}
}
