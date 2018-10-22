package softtest.rules.gcc.fault;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import softtest.ast.c.ASTArgumentExpressionList;
import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTDirectDeclarator;
import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.Node;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.ScopeType;
import softtest.interpro.c.Variable;
import softtest.rules.c.BasicStateMachine;
import softtest.rules.c.StateMachineUtils;
import softtest.summary.c.MMFetureType;
import softtest.summary.gcc.fault.MethodMMFeature;
import softtest.summary.gcc.fault.MethodMMFeatureVisitor;
import softtest.symboltable.c.LocalScope;
import softtest.symboltable.c.Scope;
import softtest.symboltable.c.Search;
import softtest.symboltable.c.SourceFileScope;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.Type.CType;
import softtest.symboltable.c.Type.CType_Pointer;

public class MLF_WRONGStateMachine extends BasicStateMachine {
	public final static String[] CALLOC_FUNCS = { "calloc", "malloc", "alloc",
        "strdup", "realloc" };
	@Override
    public void registFetureVisitors() {
        super.registFetureVisitors();
        InterContext.addSideEffectVisitor(MethodMMFeatureVisitor.getInstance());
    }
	
	public static List<FSMMachineInstance> createMLF_WRONGStateMachines(SimpleNode node, FSMMachine fsm){
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		Set<VariableNameDeclaration> reoccured = new HashSet<VariableNameDeclaration>();
		String xPath=".//UnaryExpression/PostfixExpression/PrimaryExpression[@Method='true']";
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);
		for (SimpleNode snode : evaluationResults) {
			MethodNameDeclaration methodDecl = StateMachineUtils.getMethodNameDeclaration(snode);
			if (methodDecl == null) {
				continue;
			}
			VariableNameDeclaration varDecl = null;
			if (methodDecl.getImage().equals("free")) {
				varDecl = MethodMMFeatureVisitor.findArgDeclInQual(snode);
				if (varDecl != null) {
					addFSM(snode, reoccured, list, varDecl, fsm);
				}
			}
			if (methodDecl.getMethodSummary() == null) {
				continue;
			}
			MethodMMFeature mmFeture = (MethodMMFeature)methodDecl.getMethodSummary().findMethodFeature(MethodMMFeature.class);
			if (mmFeture != null){
				HashMap<Variable, MMFetureType> mmFetures = mmFeture.getMMFetures();
				for (Variable variable : mmFetures.keySet()) {
					MMFetureType type = mmFetures.get(variable);
					if (variable.isParam() && type == MMFetureType.FREE) {
						varDecl = MethodMMFeatureVisitor.findArgDeclInQual(snode);
						if (varDecl != null) {
				            FSMMachineInstance fsmins = addFSM(snode, reoccured, list, varDecl, fsm);
				            if (fsmins != null) {
				                 fsmins.setTraceinfo(mmFeture.getDesp(variable));
				            }
				        }
					}
				}
			}
		}
		return list;
	}
	private static FSMMachineInstance addFSM(SimpleNode snode, Set<VariableNameDeclaration> reoccur, List<FSMMachineInstance> list, VariableNameDeclaration varDecl, FSMMachine fsm) {
		if (snode != null && varDecl instanceof VariableNameDeclaration && !reoccur.contains(varDecl)) {
			if (!reoccur.contains(varDecl) && !(varDecl.isParam() && varDecl.getType() instanceof CType_Pointer && CType.getOrignType(varDecl.getType()) instanceof CType_Pointer)
					&& varDecl.getScope() instanceof LocalScope)
			{
				FSMMachineInstance fsmInstance = fsm.creatInstance();
				fsmInstance.setRelatedVariable((VariableNameDeclaration)varDecl);
				fsmInstance.setRelatedASTNode(snode);
				String desp="";
				if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
					if (varDecl.getNode() != null) {
						desp = "The varibale \"" + varDecl.getImage() + "\" which defines in line "+ varDecl.getNode().getBeginLine() + " is free in line " + snode.getBeginLine();
					} else {
						desp = "The varibale \"" + varDecl.getImage() + "\" is free in line " + snode.getBeginLine();
					}

				} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
					if (varDecl.getNode() != null) {
						desp="在第 "+varDecl.getNode().getBeginLine()+" 行定义的变量 \""+varDecl.getImage()+"\"在 "+snode.getBeginLine()+" 行被释放了内存 ";
					} else {
						desp="\""+varDecl.getImage()+"\"在 "+snode.getBeginLine()+" 行被释放了内存 ";
					}
				}			
				fsmInstance.setDesp(desp);
				list.add(fsmInstance);
				reoccur.add((VariableNameDeclaration)varDecl);
				return fsmInstance;
			}
		}
		return null;
	}
	public static boolean checkCAlloc(List nodes,FSMMachineInstance fsmin){
		for (Object o : nodes) {
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
					if(varDecl == fsmin.getRelatedVariable())
						return true;
				}
			}
			if (methodDecl.getMethodSummary() == null)
				continue;
			MethodMMFeature mmFeture = (MethodMMFeature) methodDecl.getMethodSummary().findMethodFeature(MethodMMFeature.class);
			if (mmFeture == null)
				continue;
			if (mmFeture.isAllocateAndReturn())
			{
				varDecl = MethodMMFeatureVisitor.findAssginDeclInQual(snode);
				if (varDecl != null)
				{
					if(varDecl == fsmin.getRelatedVariable())
						return true;
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
							if(varDecl == fsmin.getRelatedVariable())
								return true;
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
						if(varDecl1 == fsmin.getRelatedVariable())
							return true;
					}
				}				
			}
		}
		return false;
	}
	public static boolean checkAssign(List nodes,FSMMachineInstance fsmin){
		for (Object o : nodes) {
			SimpleNode varNode = ((SimpleNode)o);
			if(!(varNode.jjtGetChild(0) instanceof ASTUnaryExpression))
				continue;
			if(!(varNode.jjtGetChild(2) instanceof ASTAssignmentExpression))
				continue;
			ASTUnaryExpression p = (ASTUnaryExpression) varNode.jjtGetChild(0);
			VariableNameDeclaration leftvar = p.getVariableDecl();
			if(leftvar == null)
			    continue;
		    if(leftvar == fsmin.getRelatedVariable())
			    return true;
		}
		return false;
	}
	
	public static boolean checkAssignByInit(List nodes,FSMMachineInstance fsmin){
		for (Object o: nodes) {
			SimpleNode varNode = (SimpleNode)o;
			ASTDirectDeclarator dnode = (ASTDirectDeclarator) varNode.getFirstChildOfType(ASTDirectDeclarator.class);
			VariableNameDeclaration leftVar = dnode.getVariableNameDeclaration();
		    if(leftVar == fsmin.getRelatedVariable())
			    return true;
		}
		return false;
	}
	
	public static boolean checkCRelease(List nodes,FSMMachineInstance fsmin){
		for (Object o : nodes) {
			if (fsmin.getRelatedASTNode() == o) {
				fsmin.setDesp(fsmin.getDesp()+"释放之前并无分配操作。");
				return true;
			}
		}
		return false;
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
	public static boolean isCAllocFunc(String funcName) {
		if (funcName == null) {
			return false;
		}
		for (int i = 0; i < CALLOC_FUNCS.length; i++) {
			if (CALLOC_FUNCS[i].equals(funcName)) {
				return true;
			}
		}
		return false;
	}
}
