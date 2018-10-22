package softtest.rules.gcc.fault;

import java.util.Collections;
import java.util.Comparator;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.VexNode;
import softtest.config.c.Config;
import softtest.domain.c.analysis.SymbolDomainSet;
import softtest.domain.c.analysis.ValueSet;
import softtest.domain.c.interval.PointerDomain;
import softtest.domain.c.interval.PointerValue;
import softtest.domain.c.symbolic.Expression;
import softtest.domain.c.symbolic.SymbolFactor;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.fsm.c.FSMStateInstance;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.Variable;
import softtest.rules.c.BasicStateMachine;
import softtest.rules.c.StateMachineUtils;
import softtest.summary.c.MMFetureType;
import softtest.summary.gcc.fault.MethodMMFeature;
import softtest.summary.gcc.fault.MethodMMFeatureVisitor;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.NameDeclaration;
import softtest.symboltable.c.SourceFileScope;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.Type.CType_AbstPointer;

/**
 * 
 * @author xwt
 * 
 */
public class MLF_FREEStateMachine extends BasicStateMachine {
	public void registFetureVisitors()
	{
		super.registFetureVisitors();
		InterContext.addSideEffectVisitor(MethodMMFeatureVisitor.getInstance());
	}
	public static List<FSMMachineInstance> createMLF_FREEStateMachines(SimpleNode node, FSMMachine fsm){
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		Set<VariableNameDeclaration> reoccured = new HashSet<VariableNameDeclaration>();
		String xPath =".//UnaryExpression/PostfixExpression/PrimaryExpression[@Method='true']";
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);
		Collections.sort(evaluationResults,new Comparator<SimpleNode>(){
	      	  public int compare(SimpleNode s1, SimpleNode s2) {
	                return s1.getBeginLine() - s2.getBeginLine();
	            }
	        });
		for (SimpleNode snode : evaluationResults) {
			MethodNameDeclaration methodDecl = StateMachineUtils.getMethodNameDeclaration(snode);
			if (methodDecl == null || methodDecl.getImage() == null) {
				continue;
			}
			NameDeclaration varDecl = null;
			if (methodDecl.getImage().equals("free")) {
				varDecl = MethodMMFeatureVisitor.findArgDeclInQual(snode);
				if (varDecl != null) {
					addFSM(snode, methodDecl, reoccured, list, varDecl, fsm);
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
				            FSMMachineInstance fsmins = addFSM(snode,methodDecl, reoccured, list, varDecl, fsm);
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
	
	private static FSMMachineInstance addFSM(SimpleNode snode, MethodNameDeclaration methodDecl, Set<VariableNameDeclaration> reoccur, List<FSMMachineInstance> list, NameDeclaration varDecl, FSMMachine fsm) {
		if (snode != null && varDecl instanceof VariableNameDeclaration && !reoccur.contains(varDecl)) {
			Variable variable = Variable.getVariable((VariableNameDeclaration) varDecl);
			if(variable!=null&&variable.isParam()){
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
						desp="在第 "+varDecl.getNode().getBeginLine()+" 行定义的变量 \""+varDecl.getImage()+"\"在 "+snode.getBeginLine()+" 行通过函数"+methodDecl.getImage()+"被释放了内存 ";
					} else {
						desp="\""+varDecl.getImage()+"\"在 "+snode.getBeginLine()+" 行通过函数"+methodDecl.getImage()+"被释放了内存 ";
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
	
	public static boolean checkFree(List nodes, FSMMachineInstance fsmin) {
		for (Object o : nodes) {
			SimpleNode snode = ((SimpleNode)o);
			if(snode instanceof ASTPrimaryExpression){
				MethodNameDeclaration methodDecl = StateMachineUtils.getMethodNameDeclaration(snode);
				if(methodDecl == null)
	    			continue;
				NameDeclaration varDecl = null;
				if (methodDecl.getImage().equals("free")) {
					varDecl = MethodMMFeatureVisitor.findArgDeclInQual(snode);
					if(varDecl == fsmin.getRelatedVariable())
						return true;
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
							if(varDecl == fsmin.getRelatedVariable())
								return true;
						}
					}
				}
			}
		}
		return false;
	}
	
	public static boolean checkGlobalVar(List nodes, FSMMachineInstance fsmin){
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
		    if(leftvar!=null && !(leftvar.getScope() instanceof SourceFileScope))
			    continue;
		    if(varNode.jjtGetChild(2) instanceof ASTAssignmentExpression){
		    	ASTAssignmentExpression a = (ASTAssignmentExpression) varNode.jjtGetChild(2);
			    ASTUnaryExpression un = (ASTUnaryExpression) a.getFirstChildOfType(ASTUnaryExpression.class);
			    if(un == null)
				    continue;
			    VariableNameDeclaration rightvar = un.getVariableDecl();
			    if(rightvar!=null){
	            	if(rightvar == fsmin.getRelatedVariable())
						return true;
	            }		    
		    }
		}
		return false;
	}
	
	public static boolean checkError(VexNode vex, FSMMachineInstance fsmin){
		if(vex.getName().startsWith("func_out")){
			fsmin.setDesp(fsmin.getDesp() + "，在函数结束时发现并不是在所有路径上都得到释放");
			return true;
		}
		return false;
	}
	
	public static void setDomain(VexNode vex, FSMMachineInstance fsmin){
		VariableNameDeclaration var = fsmin.getRelatedVariable();
		if(vex.getName().startsWith("if_head")){
			Expression value = vex.getValue(fsmin.getRelatedVariable());
			if(value != null){
				if(var.getType() instanceof CType_AbstPointer){
					Enumeration<FSMStateInstance> en = fsmin.getStates().getTable().keys();
					while(en.hasMoreElements()){
						FSMStateInstance statein = en.nextElement();
						String name = statein.getState().getName().toLowerCase();
						if("start".equalsIgnoreCase(name)){
							ValueSet vs = statein.getValueSet();
							Expression exp = vs.getValue(var);
							if(exp!=null && exp.getSingleFactor() != null && exp.getSingleFactor() instanceof SymbolFactor){
								SymbolFactor sfactor = (SymbolFactor)exp.getSingleFactor();
								SymbolDomainSet sd = statein.getSymbolDomainSet();
								PointerDomain pd = new PointerDomain(PointerValue.NOTNULL); 
								sd.addDomain(sfactor, pd);
							}
						}
					}
				}
			}
		}
	}

}
