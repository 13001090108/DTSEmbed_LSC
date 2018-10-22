package softtest.rules.gcc.fault;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import softtest.ast.c.ASTArgumentExpressionList;
import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTConditionalExpression;
import softtest.ast.c.ASTEqualityExpression;
import softtest.ast.c.ASTLogicalANDExpression;
import softtest.ast.c.ASTLogicalORExpression;
import softtest.ast.c.ASTPostfixExpression;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTStatement;
import softtest.ast.c.ASTStatementList;
import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.AbstractExpression;
import softtest.ast.c.Node;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.VexNode;
import softtest.config.c.Config;
import softtest.domain.c.analysis.ConditionData;
import softtest.domain.c.analysis.ConditionDomainVisitor;
import softtest.domain.c.analysis.ExpressionValueVisitor;
import softtest.domain.c.analysis.ExpressionVistorData;
import softtest.domain.c.analysis.SymbolDomainSet;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.DomainType;
import softtest.domain.c.interval.IntegerDomain;
import softtest.domain.c.interval.PointerDomain;
import softtest.domain.c.interval.PointerValue;
import softtest.domain.c.symbolic.Expression;
import softtest.domain.c.symbolic.Factor;
import softtest.domain.c.symbolic.IntegerFactor;
import softtest.domain.c.symbolic.SymbolFactor;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.Method;
import softtest.interpro.c.Variable;
import softtest.rules.c.BasicStateMachine;
import softtest.rules.c.StateMachineUtils;
import softtest.summary.c.MethodFeature;
import softtest.summary.c.MethodSummary;
import softtest.summary.gcc.fault.MethodNPDPreCondition;
import softtest.summary.gcc.fault.MethodNPDPreConditionVisitor;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.NameDeclaration;
import softtest.symboltable.c.NameOccurrence;
import softtest.symboltable.c.Scope;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.NameOccurrence.OccurrenceType;
import softtest.symboltable.c.Type.CType;

public class NPD_PREStateMachine extends BasicStateMachine {

	@Override
	public void registFetureVisitors() {
		super.registFetureVisitors();
		InterContext.addPreConditionVisitor(MethodNPDPreConditionVisitor.getInstance());
	}

	/** 对于每一个指针出现的节点，创建空指针状态机实例 */
	//modified by nmh
	//去掉了HashSet<VariableNameDeclaration> npdSet（记录加入到状态机中的参数）。这个没有必要。
	//因为可能一个参数在一个函数中被一个或多个函数调用多次
	public static List<FSMMachineInstance> createNPDStateMachines(SimpleNode node, FSMMachine fsm) {

		List<FSMMachineInstance> list = new ArrayList<FSMMachineInstance>();
 		String xPath = ".//PrimaryExpression[@Method='true']";
		List<SimpleNode> nodes = StateMachineUtils.getEvaluationResults(node, xPath);
		//HashSet<VariableNameDeclaration> npdSet = new HashSet<VariableNameDeclaration>(1);
		for (SimpleNode exp : nodes) {
			// 获取所有的本地调用方法声明
			AbstractExpression funcNode = (AbstractExpression)exp;
			if (!funcNode.isMethod()) {
				continue;
			}
			MethodNameDeclaration methodDecl = null;
			if (exp instanceof ASTPrimaryExpression) {
				methodDecl = (MethodNameDeclaration)((ASTPrimaryExpression)exp).getMethodDecl();
			} 
			if (methodDecl == null) {
				continue;
			}
			Method method = methodDecl.getMethod();
			if (method == null) {
				continue;
			}
			// 从函数摘要中NPD的前置条件中，对每个形参建立相应的检测自动机
			if (methodDecl.getMethod() != null) {
				MethodSummary summary =  method.getMtSummmary();
				if (summary == null) {
					continue;
				}
			
				//对于变参的系统函数单独特殊处理,此处为sscanf
				
				if(methodDecl.getImage().equals("sscanf"))
				{
					
						ASTPostfixExpression postfix = null;
			             if (exp.jjtGetParent() instanceof ASTPostfixExpression) {
							postfix = (ASTPostfixExpression) exp.jjtGetParent();
						}
						if (postfix == null) {
							return null;
						}	
						ASTArgumentExpressionList argExpList =(ASTArgumentExpressionList) postfix.findDirectChildOfType(ASTArgumentExpressionList.class,0);
						if (argExpList == null ) {
							return null;
						}
						int childNumber = argExpList.jjtGetNumChildren();
						//只关心sscanf的最后一个子孩子是否为空
						
						ASTAssignmentExpression lastChildNode =(ASTAssignmentExpression) argExpList.findDirectChildOfType(ASTAssignmentExpression.class, childNumber-1);
						if (lastChildNode!= null ) {
							List<Node> primaryNodes = lastChildNode.findChildrenOfType(ASTPrimaryExpression.class);
							if (primaryNodes.size() >0) {
								if(primaryNodes.get(0) instanceof ASTPrimaryExpression)
								{
									ASTPrimaryExpression pExp = (ASTPrimaryExpression) primaryNodes.get(0);
									if(pExp.getDescendantDepth()<1)
									{
										VariableNameDeclaration var1 =(VariableNameDeclaration) pExp.getVariableNameDeclaration();
										CType type = var1.getType();
										if( (type!=null) && (type.isPointType())) 
									{
//											Domain pDomain = var1.getDomain();
//											if (pDomain != null && !pDomain.isUnknown() && pDomain instanceof PointerDomain && pDomain.getDomaintype() != DomainType.UNKNOWN) {
//												PointerDomain point = (PointerDomain)pDomain;
//												if (point.isCanonical() && point.getValue() == PointerValue.NULL ) {
													FSMMachineInstance fsmInstance = fsm.creatInstance();
													fsmInstance.setRelatedASTNode(exp);
													fsmInstance.setRelatedVariable(var1);
													fsmInstance.setStateData(var1.getVariable());
													list.add(fsmInstance);	
											//	}
											}
									
									}
								}
							}
						}
				}
							
					
						

		Set<MethodFeature> features = summary.getPreConditions();
				
				for (MethodFeature feature : features) {
					if (feature instanceof MethodNPDPreCondition) {
						MethodNPDPreCondition npdPreCond = (MethodNPDPreCondition)feature;
						Set<Variable> npdVars = npdPreCond.getNPDVariables();
						for (Variable var : npdVars) {
							if (var.isParam()) { // NPD对参数的约束
								VariableNameDeclaration paramDecl = findSingleParam(exp, var);
								if (paramDecl != null) {
									//if (!npdSet.contains(paramDecl)) {
										FSMMachineInstance fsmInstance = fsm.creatInstance();
										fsmInstance.setRelatedASTNode(exp);
										fsmInstance.setStateData(var);
										if (!methodDecl.isLib()) {
											fsmInstance.setTraceinfo(npdPreCond.getDespString(var));
										}
										//npdSet.add(paramDecl);
										fsmInstance.setRelatedVariable(paramDecl);
										list.add(fsmInstance);
									//}

								} else {
									FSMMachineInstance fsmInstance = fsm.creatInstance();
									fsmInstance.setRelatedASTNode(exp);
									fsmInstance.setStateData(var);
									if (!methodDecl.isLib()) {
										fsmInstance.setTraceinfo(npdPreCond.getDespString(var));
									}
									list.add(fsmInstance);
								}
							} else { // NPD对全局或者成员变量的约束
								VariableNameDeclaration varDecl = findLocalVariableDecl(var, node);
								if (varDecl == null) {
									continue;
								}
								//if (!npdSet.contains(varDecl)) {
									FSMMachineInstance fsmInstance = fsm.creatInstance();
									fsmInstance.setRelatedASTNode(exp);
									fsmInstance.setRelatedVariable(varDecl);
									fsmInstance.setStateData(var);
									fsmInstance.setResultString(npdPreCond.getDespString(var));
									fsmInstance.setTraceinfo(npdPreCond.getDespString(var));
									list.add(fsmInstance);
									//npdSet.add(varDecl);
								//}
							}
						}
					}
				}
			}
		}
		return list;
	}
	
	private static VariableNameDeclaration findSingleParam(SimpleNode t, Variable npdVar) {
		int argIndex = -1;
		SimpleNode argNode = null;
		if (t instanceof ASTPrimaryExpression) {
			ASTPostfixExpression postfix = null;
             if (t.jjtGetParent() instanceof ASTPostfixExpression) {
				postfix = (ASTPostfixExpression) t.jjtGetParent();
			}
			if (postfix == null) {
				return null;
			}
			
			// 获取形参节点，在这儿只考虑postfix里面只有一次函数调用
			List re = postfix.findDirectChildOfType(ASTArgumentExpressionList.class);
			if (re == null || re.size() <=0 ) {
				return null;
			}
			
			argNode = (ASTArgumentExpressionList)re.get(0);
//			
			argIndex = npdVar.getParamIndex();
			if (argIndex < 0 || argIndex >= argNode.jjtGetNumChildren()) {
				return null;
			}
			List<Node> varsNode = argNode.findChildrenOfType(ASTAssignmentExpression.class);
			if (varsNode.size() > argIndex) {
				ASTAssignmentExpression ass = (ASTAssignmentExpression) argNode.jjtGetChild(argIndex);
				if (ass!= null ) {
					List<Node> nodes = ass.findChildrenOfType(ASTPrimaryExpression.class);
					if (nodes.size() >0) {
						return ((SimpleNode) nodes.get(0)).getVariableNameDeclaration();
					}
				}
				
			}
		} 
		return null;
	}
	
	
	private static VariableNameDeclaration findLocalVariableDecl(Variable variable, SimpleNode node) {
		Scope scope = node.getScope().getEnclosingClassScope();
		if (scope == null) {
			scope = node.getScope().getEnclosingSourceFileScope();
		}
		if (scope != null) {
			Set<VariableNameDeclaration> vars = scope.getVariableDeclarations().keySet();
			for (VariableNameDeclaration var : vars) {
				if (var.getVariable() == variable) {
					return var;
				}
			}
		}
		return null;
	}

	/**
	 * 添加对全局的空指针检测，主要包含两种情况
	 * 1. func(a)    在func函数里面有对a的直接指针引用，a为NULL时有NPD可能性
	 * 2. func(g())  在func函数里面有对a的直接指针引用，g()返回值为NULL时有NPD可能性
	 * @param nodes
	 * @param fsmin
	 * @return
	 */
	//不明白checkMethodNpd和checkMethodNpdNUll这两个方法有什么区别 ---nmh
	public static boolean checkMethodNpd(List nodes, FSMMachineInstance fsmin) {
		Iterator it = nodes.iterator();
		while (it.hasNext()) {
			SimpleNode t = (SimpleNode)it.next();
			if (fsmin.getRelatedASTNode() != t) {
				continue;
			}
			// 在函数调用处，检测被调用的函数的实参是否满足形参的NPD前置约束
			Variable npdVar = (Variable)fsmin.getStateData();
			if (npdVar.isParam()) {
				int argIndex = -1;
				SimpleNode argNode = null;
				MethodNameDeclaration methodDecl = null;
				if (t instanceof ASTPrimaryExpression) {
					ASTPrimaryExpression node = (ASTPrimaryExpression)t;
					methodDecl = (MethodNameDeclaration)node.getMethodDecl();
					ASTPostfixExpression postfix = null;
					if (node.jjtGetParent() instanceof ASTPrimaryExpression) {
						postfix = (ASTPostfixExpression) node.jjtGetParent().jjtGetParent();
					} else if (node.jjtGetParent() instanceof ASTPostfixExpression) {
						postfix = (ASTPostfixExpression) node.jjtGetParent();
					}
					if (postfix == null) {
						continue;
					}
					
					// 获取形参节点，在这儿只考虑postfix里面只有一次函数调用
					List re = postfix.findDirectChildOfType(ASTArgumentExpressionList.class);
					if (re == null || re.size() <=0 ) {
						continue;
					}
					
					argNode = (ASTArgumentExpressionList)re.get(0);				
					argIndex = npdVar.getParamIndex();
//					//bug && changed to || by suntao
					if (argIndex < 0 || argIndex >= argNode.jjtGetNumChildren()) {
						continue;
					}
				} 

				if (argIndex != -1) {
					ExpressionValueVisitor exp = new ExpressionValueVisitor();
					ExpressionVistorData domaindata = new ExpressionVistorData();
					domaindata.currentvex = argNode.getCurrentVexNode();
					exp.visit((SimpleNode)argNode.jjtGetChild(argIndex), domaindata);		
					Expression value1 = domaindata.value;
					Domain mydomain=null;
					if(value1!=null)
					mydomain = value1.getDomain(domaindata.currentvex.getSymDomainset());
					if (((SimpleNode)argNode.jjtGetChild(argIndex)).getVariableNameDeclaration() == null) {
						if (mydomain !=null && !mydomain.isUnknown() && mydomain instanceof PointerDomain) {
							PointerDomain pd = (PointerDomain) mydomain;
							if (pd.getValue() == PointerValue.NULL) {
								return true;
							}
						}
						continue;
					}
					/*
					VariableNameDeclaration va = ((SimpleNode)argNode.jjtGetChild(argIndex)).getVariableNameDeclaration();
					if (va != null && va.isParam() && va.getScope() != null) {
						List<NameOccurrence> occ = va.getScope().getVariableDeclarations().get(va);
						if (occ!= null) {
							boolean hasDef = false;
							for(NameOccurrence o :occ) {
								if (o.getOccurrenceType() == OccurrenceType.DEF) {
									hasDef = true;
									break;
								}
								if (o.getOccurrenceType()== null && o.getLocation() != null) {
								    ASTPrimaryExpression pr = (ASTPrimaryExpression) fsmin.getRelatedASTNode();
								    List<Node> nods = ((SimpleNode) pr.jjtGetParent()).findChildrenOfType(ASTPrimaryExpression.class);
								    if (!nods.contains(o.getLocation())) {
										hasDef = true;
										break;
								    }
								}
							}
							if (!hasDef) {
								continue;
							}
						}
					}
                    */
					if (!(domaindata.currentvex.getDomain(((SimpleNode)argNode.jjtGetChild(argIndex)).getVariableNameDeclaration()) instanceof PointerDomain)) {
						Domain domain = domaindata.currentvex.getDomain(((SimpleNode)argNode.jjtGetChild(argIndex)).getVariableNameDeclaration());
						//add by suntao 对函数NPD约束的参数，若传NULL值，则报告NPD
                        //CType type = methodDecl.getParamType(argIndex);
						CType type = methodDecl.getParams().get(argIndex);
                        if(type == null || !type.equals(npdVar.getType())) {
                            continue;
                        }
                        if(domain !=null && domain.isUnknown())
                        	continue;
					}
					Domain domain = domaindata.currentvex.getDomain(((SimpleNode)argNode.jjtGetChild(argIndex)).getVariableNameDeclaration());
					if (!(domain instanceof PointerDomain)) {
						continue;
					}
					PointerDomain pd = (PointerDomain) domain; 
				    if (pd != null && !pd.isUnknown()&&(pd.getValue() == PointerValue.NULL || pd.getValue() == PointerValue.NULL_OR_NOTNULL)) {
						if (Config.TRACE) {
							System.err.println("NPD  Parameter");
						}
						VariableNameDeclaration varr= ((SimpleNode)argNode.jjtGetChild(argIndex)).getVariableNameDeclaration();
						if (varr!= null) {
							if (!confirmNPD((SimpleNode)argNode.jjtGetChild(argIndex), varr) ) {
								continue;
							}
							fsmin.setRelatedVariable((VariableNameDeclaration)varr);
							fsmin.setDesp("方法\"" + methodDecl.getImage()+"\"的第"+ (argIndex + 1) + " 个参数可能为空指针");
							return true;
						} 
					}
				}
			} else {
				// 函数调用处，会产生副作用，改变成员变量值，导致NPD
				if (fsmin.getRelatedVariable() != null && t.getCurrentVexNode() != null) {
					VexNode vexNode = t.getCurrentVexNode();
					ExpressionValueVisitor exp = new ExpressionValueVisitor();
					ExpressionVistorData domaindata = new ExpressionVistorData();
					domaindata.currentvex = t.getCurrentVexNode();
					exp.visit(t, domaindata);
					
					SymbolDomainSet domainSet = domaindata.currentvex.getSymDomainset();
					if (domainSet == null) {
						continue;
					}
					Domain domain =vexNode.getDomain(fsmin.getRelatedVariable());
					
					if (domain !=null && !domain.isUnknown() && domain instanceof PointerDomain) {
						PointerDomain pDomain = (PointerDomain)domain;
						if (pDomain.getValue() == PointerValue.NULL || pDomain.getValue() == PointerValue.NULL_OR_NOTNULL) {
							fsmin.setDesp("变量\"" + fsmin.getRelatedVariable().getImage() + "\"在调用函数的时候可能为空指针");
							fsmin.setResultString("");
							return true;
						}
					}
				}
			}
		}
		return false;
	}

	/**
	 * @return
	 */
	public static boolean checkMethodNpdNUll(List nodes, FSMMachineInstance fsmin) {
		Iterator it = nodes.iterator();
		SimpleNode sn = fsmin.getRelatedASTNode();

		while (it.hasNext()) {
			SimpleNode t = (SimpleNode)it.next();
//			if (fsmin.getRelatedASTNode() != t) {
//				continue;
//			} 
			// 在函数调用处，检测被调用的函数的实参是否满足形参的NPD前置约束
			Variable npdVar = (Variable)fsmin.getStateData();
			if (npdVar!=null && npdVar.isParam()) {
				int argIndex = -1;
				SimpleNode argNode = null;
				MethodNameDeclaration methodDecl = null;
				if ((t instanceof ASTPrimaryExpression) && t== sn) {
					ASTPrimaryExpression node = (ASTPrimaryExpression)t;
					methodDecl = (MethodNameDeclaration)node.getMethodDecl();
					ASTPostfixExpression postfix = null;
					if (node.jjtGetParent() instanceof ASTPrimaryExpression) {
						postfix = (ASTPostfixExpression) node.jjtGetParent().jjtGetParent();
					} else if (node.jjtGetParent() instanceof ASTPostfixExpression) {
						postfix = (ASTPostfixExpression) node.jjtGetParent();
					}
					if (postfix == null) {
						continue;
					}
					
					// 获取形参节点，在这儿只考虑postfix里面只有一次函数调用
					List re = postfix.findDirectChildOfType(ASTArgumentExpressionList.class);
					if (re == null || re.size() <=0 ) {
						continue;
					}
					
					argNode = (ASTArgumentExpressionList)re.get(0);				
					argIndex = npdVar.getParamIndex();
//					//bug && changed to || by suntao
					if (argIndex < 0 || argIndex >= argNode.jjtGetNumChildren()) {
						continue;
					}
				} 
				if (argIndex != -1) {
					ExpressionValueVisitor exp = new ExpressionValueVisitor();
					ExpressionVistorData domaindata = new ExpressionVistorData();
					domaindata.currentvex = argNode.getCurrentVexNode();
					exp.visit((SimpleNode)argNode.jjtGetChild(argIndex), domaindata);		
					Expression value1 = domaindata.value;
					Domain mydomain=null;
					if(value1!=null)
					    mydomain = value1.getDomain(domaindata.currentvex.getSymDomainset());
					if (((SimpleNode)argNode.jjtGetChild(argIndex)).getVariableNameDeclaration() == null) {
						if (mydomain!=null && !mydomain.isUnknown() && mydomain instanceof PointerDomain) {
							PointerDomain pd = (PointerDomain) mydomain;
							if (pd.getValue() == PointerValue.NULL || pd.getValue() == PointerValue.NULL_OR_NOTNULL) {
								fsmin.setDesp("方法\"" + methodDecl.getImage()+"\"的第"+ (argIndex + 1) + " 个参数可能为空指针");
								return true;
							}
						}
						if (mydomain!=null && !mydomain.isUnknown() && mydomain instanceof IntegerDomain) {
							IntegerDomain id = (IntegerDomain) mydomain;
							if (id.contains(0)) {
								fsmin.setDesp("方法\"" + methodDecl.getImage()+"\"的第"+ (argIndex + 1) + " 个参数可能为空指针");
								return true;
							}
						}
						continue;
					}
				}
			} else {
				// 函数调用处，会产生副作用，改变成员变量值，导致NPD
				if (fsmin.getRelatedVariable() != null && t.getCurrentVexNode() != null) {
					VexNode vexNode = t.getCurrentVexNode();
					ExpressionValueVisitor exp = new ExpressionValueVisitor();
					ExpressionVistorData domaindata = new ExpressionVistorData();
					domaindata.currentvex = t.getCurrentVexNode();
					exp.visit(t, domaindata);
					
					SymbolDomainSet domainSet = domaindata.currentvex.getSymDomainset();
					if (domainSet == null) {
						continue;
					}
					Domain domain =vexNode.getDomain(fsmin.getRelatedVariable());
					if (domain !=null && !domain.isUnknown() && domain instanceof PointerDomain) {
						PointerDomain pDomain = (PointerDomain)domain;
						if (pDomain.getValue() == PointerValue.NULL || pDomain.getValue() == PointerValue.NULL_OR_NOTNULL) {
							fsmin.setDesp("变量\"" + fsmin.getRelatedVariable().getImage() + "\"在调用函数的时候可能为空指针");
							fsmin.setResultString("");
							return true;
						}
					}
				}
			}
		}
		return false;
	}
	
	public static boolean confirmNPD(SimpleNode idExp, VariableNameDeclaration vDecl) {
		//check the condition expression eg: int j = (p == 0)? i: *p;
		ASTConditionalExpression con = (ASTConditionalExpression) idExp.getFirstParentOfType(ASTConditionalExpression.class);
		if (con != null) {
			String str = "./PostfixExpression/PrimaryExpression";
			List evaluationResults = StateMachineUtils.getEvaluationResults((SimpleNode)con.jjtGetChild(0), str);
			Iterator iterList = evaluationResults.listIterator();
			while(iterList.hasNext()){
				ASTPrimaryExpression temp = (ASTPrimaryExpression) iterList.next();
				if(temp.getVariableDecl()!= vDecl){
					continue;
				}
				ASTEqualityExpression equal = (ASTEqualityExpression)temp.getFirstParentOfType(ASTEqualityExpression.class);
				if(equal == null || equal.jjtGetNumChildren()>1){
					return false;
				}					
			}
		}
		// 检查表达式短路: if (p!=null && *p==1) 或者 if (p && *p==1)
		ASTLogicalANDExpression expressionAnd = (ASTLogicalANDExpression)idExp.getFirstParentOfType(ASTLogicalANDExpression.class);
		if (expressionAnd != null && expressionAnd.jjtGetNumChildren() >= 2) {
			for (int i = 0; i < expressionAnd.jjtGetNumChildren(); i++) {
				SimpleNode expNode = (SimpleNode)expressionAnd.jjtGetChild(i);
				if (idExp.isSelOrAncestor(expNode)) {
					break;
				}
				
				// p 的may集合是不是为非空
				ConditionDomainVisitor condVisitor = new ConditionDomainVisitor();
				ConditionData condData = new ConditionData(idExp.getCurrentVexNode());
				expNode.jjtAccept(condVisitor, condData);
				Domain pDomain = null;
				if(condData!=null && vDecl != null && idExp.getCurrentVexNode().getValue(vDecl) != null && idExp.getCurrentVexNode().getValue(vDecl).getSingleFactor() != null )
				{
					Factor f=idExp.getCurrentVexNode().getValue(vDecl).getSingleFactor();
					if(f.getType().getName().equals("int"))
 					{
 						IntegerFactor intFactor=(IntegerFactor)f;
 						if(intFactor.getValue()==0)
 						{
 							return false;
 						}
 					}
 						
					pDomain = condData.getMayDomain((SymbolFactor)f);
				}
				  if (pDomain != null && !pDomain.isUnknown()&& pDomain instanceof PointerDomain && pDomain.getDomaintype() != DomainType.UNKNOWN) {
					PointerDomain point = (PointerDomain)pDomain;
					if (point.getValue() == PointerValue.EMPTY || !point.offsetRange.contains(0)) {
						return false;
					}
				}
				// 判断是否有恒假分支
				ExpressionValueVisitor exp = new ExpressionValueVisitor();
				ExpressionVistorData domaindata = new ExpressionVistorData();
				domaindata.currentvex = idExp.getCurrentVexNode();
				exp.visit((SimpleNode)idExp.jjtGetChild(0), domaindata);
//				if (domaindata.currentvex.getDomain((VariableNameDeclaration)idExp.getVariableNameDeclaration()) instanceof BooleanDomain && !domaindata.domain.isUnknown()) {
//					BooleanDomain bDomain = (BooleanDomain)domaindata.domain;
//					if (bDomain.getValue() == BooleanValue.FALSE) {
//						return false;
//					}
//				} else
				Domain domain =domaindata.currentvex.getDomain((VariableNameDeclaration)idExp.getVariableNameDeclaration());
				if (domain instanceof IntegerDomain && !domain.isUnknown() && domain.getDomaintype() != DomainType.UNKNOWN) {
					IntegerDomain iDomain = (IntegerDomain)domain;
					if (iDomain.isCanonical() && iDomain.jointoOneInterval().getMin() == 0) {
						return false;
					}
				}
			}
		}
		// 检查表达式短路: if(!p || *p==1) 或者 if (p == (void*)0 || *p==1)  
		ASTLogicalORExpression expressionOr = (ASTLogicalORExpression)idExp.getFirstParentOfType(ASTLogicalORExpression.class);
		if (expressionOr != null && expressionOr.jjtGetNumChildren() >= 2) {
			for (int i = 0; i < expressionOr.jjtGetNumChildren(); i++) {
				SimpleNode expNode = (SimpleNode)expressionOr.jjtGetChild(i);
				if (idExp.isSelOrAncestor(expNode)) {
					break;
				}
				
				// p 的must集合是是空
				ConditionDomainVisitor condVisitor = new ConditionDomainVisitor();
				ConditionData condData = new ConditionData(idExp.getCurrentVexNode());
				expNode.jjtAccept(condVisitor, condData);
				if (idExp.getCurrentVexNode().getValue(vDecl) == null || idExp.getCurrentVexNode().getValue(vDecl).getSingleFactor() == null) {
					continue;
				}
				if (!(idExp.getCurrentVexNode().getValue(vDecl).getSingleFactor() instanceof SymbolFactor)) {
					continue;
				}
				Domain pDomain = condData.getMayDomain((SymbolFactor) idExp.getCurrentVexNode().getValue(vDecl).getSingleFactor());
				if (pDomain != null && !pDomain.isUnknown()&& pDomain instanceof PointerDomain && pDomain.getDomaintype() != DomainType.UNKNOWN) {
					PointerDomain point = (PointerDomain)pDomain;
					if (point.isCanonical() && point.offsetRange.contains(0) ) {
						return false;
					}
				}
				// 判断是否有恒真分支
				ExpressionValueVisitor exp = new ExpressionValueVisitor();
				ExpressionVistorData domaindata = new ExpressionVistorData();
				domaindata.currentvex = idExp.getCurrentVexNode();
				exp.visit((SimpleNode)idExp.jjtGetChild(0), domaindata);
//				if (domaindata.domain instanceof BooleanDomain && !domaindata.domain.isUnknown()) {
//					BooleanDomain bDomain = (BooleanDomain)domaindata.domain;
//					if (bDomain.getValue() == BooleanValue.TRUE) {
//						return false;
//					}
//				} else
				Domain domain =domaindata.currentvex.getDomain((VariableNameDeclaration)idExp.getVariableNameDeclaration());
				if (domain instanceof IntegerDomain && !domain.isUnknown() && domain.getDomaintype() != DomainType.UNKNOWN) {
					IntegerDomain iDomain = (IntegerDomain)domain;
					if (iDomain.isCanonical() && iDomain.jointoOneInterval().getMin() == 0) {
						return false;
					}
				}
			}
		}
		
		// 确保不是sizeof(*p)
		boolean isSizeof = false;
		SimpleNode node = (SimpleNode)idExp.jjtGetParent();
		while (!(node instanceof ASTStatement) && node.jjtGetNumChildren() <= 2) {
			if (node instanceof ASTUnaryExpression && node.getImage().equals("sizeof")) {
				isSizeof = true;
				break;
			} else if (node instanceof ASTAssignmentExpression && node.jjtGetNumChildren() >= 2) {
				break;
			}
			node = (SimpleNode)node.jjtGetParent();
		}
		if (isSizeof) {
			return false;
		}
		return true;
	}
	public static boolean checkFollowed(VexNode node,FSMMachineInstance fsmin){
		if(fsmin.getRelatedVariable()==null)
			return false;
		String var=((VariableNameDeclaration)fsmin.getRelatedVariable()).getImage();	
		SimpleNode simnode=node.getTreenode();
		Domain pDomain=node.getDomain((VariableNameDeclaration)fsmin.getRelatedVariable());
		boolean isUnknowPoint=false;
		if(pDomain instanceof PointerDomain && !pDomain.isUnknown()&& pDomain.getDomaintype() == DomainType.UNKNOWN){
			isUnknowPoint=true;
		}
		ASTStatementList stat_list=(ASTStatementList)simnode.getFirstParentOfType(ASTStatementList.class);
		if(stat_list!=null && isUnknowPoint){
			String xpath=".//SelectionStatement/Expression/SssignmentExpression//UnaryExpression[./UnaryOperator[@Image='!']]/UnaryExpression/PostfixExpression[count(*)<=1]/PrimaryExpression[@Image='"+var+"']"
			+"|.//SelectionStatement/Expression/SssignmentExpression/pm_expression/UnaryExpression/PostfixExpression[count(*)<=1]/PrimaryExpression[@Image='"+var+"']";
			List evaluationResults = StateMachineUtils.getEvaluationResults(stat_list, xpath);	
			Iterator iter=evaluationResults.iterator();
			while(iter.hasNext()){
				ASTPrimaryExpression idexp=(ASTPrimaryExpression)iter.next();
				if(node!=idexp.getCurrentVexNode()){
					//pDomain.setUnknown(false);
					//node.addDomain((VariableNameDeclaration)fsmin.getRelatedVariable(), pDomain);
					return true;
				}
			}
		}
		return false;
	}
}
