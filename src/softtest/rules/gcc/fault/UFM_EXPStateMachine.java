package softtest.rules.gcc.fault;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import softtest.ast.c.ASTArgumentExpressionList;
import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTConstant;
import softtest.ast.c.ASTEqualityExpression;
import softtest.ast.c.ASTPostfixExpression;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.Node;
import softtest.ast.c.SimpleNode;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.Variable;
import softtest.rules.c.BasicStateMachine;
import softtest.rules.c.StateMachineUtils;
import softtest.summary.c.MMFetureType;
import softtest.summary.c.MethodFeature;
import softtest.summary.c.MethodSummary;
import softtest.summary.gcc.fault.MethodMMFeature;
import softtest.summary.gcc.fault.MethodMMFeatureVisitor;
import softtest.summary.gcc.fault.MethodUFMPostCondition;
import softtest.summary.gcc.fault.MethodUFMPostConditionVisitor;
import softtest.summary.gcc.fault.MethodUFMPreCondition;
import softtest.summary.gcc.fault.MethodUFMPreConditionVisitor;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.NameDeclaration;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.Type.CType_Pointer;

/**
 * 检测悬挂指针类型故障
 * @author cjie
 * 
 */
public class UFM_EXPStateMachine extends BasicStateMachine {

	@Override
	public void registFetureVisitors() {
		super.registFetureVisitors();
		InterContext.addPreConditionVisitor(MethodUFMPreConditionVisitor.getInstance());
		InterContext.addPostConditionVisitor(MethodUFMPostConditionVisitor.getInstance());
		InterContext.addPostConditionVisitor(MethodMMFeatureVisitor.getInstance());
	}

	public static List<FSMMachineInstance> createUFM_EXPStateMachines(
			SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		//gcc无new, delete关键字
//		String xPath =".//delete_expression/unary_expression/postfix_expression[count(*)=1]/primary_expression/id_expression";
//		List<SimpleNode> result =StateMachineUtils.getEvaluationResults(node, xPath);
		Set<VariableNameDeclaration> reoccured = new HashSet<VariableNameDeclaration>();
//		for (SimpleNode snode : result) {
//			ASTid_expression idExp = (ASTid_expression)snode;
//			NameDeclaration decl = idExp.getNameDeclaration();
//			if (decl != null) {
//				addFSM(idExp, reoccured, list, decl, fsm);
//			}
//		}
		// 函数调用时候建立状态机实例
		String xPath=".//PostfixExpression/PrimaryExpression[@Method='true']";
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);
		for (SimpleNode snode : evaluationResults) {
			//MethodNameDeclaration mnd=((ASTPrimaryExpression)snode).getMethodDecl();
			MethodNameDeclaration methodDecl = StateMachineUtils.getMethodNameDeclaration(snode);
			if (methodDecl == null || methodDecl.getImage() == null) {
				continue;
			}
			
			NameDeclaration varDecl = null;
			if (methodDecl.getImage().equals("free")) {
				/**modified by xwt 2011.7.1*/
				if(snode.jjtGetParent() instanceof ASTPostfixExpression){
					if(snode.jjtGetParent().jjtGetNumChildren() == 2){
						ASTArgumentExpressionList ae = (ASTArgumentExpressionList) snode.getNextSibling();
						ASTUnaryExpression ue = (ASTUnaryExpression) ae.getFirstChildOfType(ASTUnaryExpression.class);
						varDecl = ue.getVariableDecl();
					}
					else
						continue;
				}
				/*List<Node> argNodes = ((SimpleNode) snode.jjtGetParent()).findChildrenOfType(ASTPrimaryExpression.class);
				if( argNodes == null || argNodes.size() != 2) {
					continue;
				}
				if (argNodes.get(1) instanceof ASTPrimaryExpression && argNodes.get(1).jjtGetParent().jjtGetNumChildren() == 1) {
					varDecl = ((ASTPrimaryExpression)argNodes.get(1)).getVariableDecl();
				}*/

				if (varDecl != null) {
					addFSM(snode, methodDecl, reoccured, list, varDecl, fsm);
				}
				continue;
			}
			if (methodDecl.getMethodSummary() == null) {
				continue;
			}
			MethodMMFeature mmFeture = (MethodMMFeature)methodDecl.getMethodSummary().findMethodFeature(MethodMMFeature.class);
			if (mmFeture != null) {
			    HashMap<Variable, MMFetureType> mmFetures = mmFeture.getMMFetures();
			    for (Variable variable : mmFetures.keySet()) {
			        MMFetureType type = mmFetures.get(variable);
			        if (variable.isParam() &&   type == MMFetureType.FREE) {
//			            if (snode instanceof ASTqualified_id) {
//			                varDecl = MethodMMFeatureVisitor.findArgDeclInQual(snode);
//			            } else 
			            if (snode instanceof ASTPrimaryExpression && snode.jjtGetParent().jjtGetNumChildren() >1 && snode.jjtGetParent().jjtGetChild(1) instanceof ASTArgumentExpressionList) {
			                varDecl = MethodMMFeatureVisitor.getArgDecl((ASTArgumentExpressionList)snode.jjtGetParent().jjtGetChild(1), variable.getParamIndex());
			            }
			            if (varDecl != null) {
			                FSMMachineInstance fsmins = addFSM(snode, methodDecl,reoccured, list, varDecl, fsm);
			                if (fsmins != null) {
			                    fsmins.setTraceinfo(mmFeture.getDesp(variable));
			                }
			            }
			        }
			    }
			}
            //add post condition by suntao
            MethodUFMPostCondition post = (MethodUFMPostCondition) methodDecl.getMethodSummary().findMethodFeature(MethodUFMPostCondition.class);
            if(post == null) {
                continue;
            }
			for(Variable var : post.getUFMVariables()) {
                FSMMachineInstance fsmInstance = fsm.creatInstance();
                fsmInstance.setRelatedASTNode(snode);
                fsmInstance.setReleatedVexNode(snode.getCurrentVexNode());
                fsmInstance.setStateData(var);
                fsmInstance.setDesp("变量" + var.getName() + "在"+snode.getEndLine()+"行函数" + methodDecl.getImage() + "被调用后已被释放");
                list.add(fsmInstance);
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
			if (argIndex < 0 && argIndex >= argNode.jjtGetNumChildren()) {
				return null;
			}
			List<Node> varsNode = argNode.findChildrenOfType(ASTPrimaryExpression.class);
			if (varsNode.size() > argIndex) {
				return ((SimpleNode)varsNode.get(argIndex)).getVariableNameDeclaration();
			}
		} 
		return null;
	}
	private static FSMMachineInstance addFSM(SimpleNode snode, MethodNameDeclaration methodDecl, Set<VariableNameDeclaration> reoccur, List<FSMMachineInstance> list, NameDeclaration varDecl, FSMMachine fsm) {
		if (snode != null && varDecl instanceof VariableNameDeclaration && !reoccur.contains(varDecl)) {
			FSMMachineInstance fsmInstance = fsm.creatInstance();
			fsmInstance.setRelatedVariable((VariableNameDeclaration)varDecl);
			fsmInstance.setRelatedASTNode(snode);
			String desp="";
			if (varDecl.getNode() != null) {
				desp="在第 "+varDecl.getNode().getBeginLine()+" 行定义的变量 \""+varDecl.getImage()+"\"在 "+snode.getBeginLine()+" 行通过函数"+methodDecl.getImage()+"被释放了内存 ";
			} else {
				desp="\""+varDecl.getImage()+"\"在 "+snode.getBeginLine()+" 行被释放了内存 ";
			}
			fsmInstance.setDesp(desp);
			list.add(fsmInstance);
			reoccur.add((VariableNameDeclaration)varDecl);
			return fsmInstance;
		}
		return null;
	}
	
	public static boolean checkFree(List nodes, FSMMachineInstance fsmin) {
		Iterator it = nodes.iterator();
		while (it.hasNext()) {
			SimpleNode idNode = (SimpleNode) it.next();
			if(fsmin.getRelatedASTNode() == idNode){
				return true;
			}
		}
		return false;
	}
	
	public static boolean checkAssign(List nodes, FSMMachineInstance fsmin) {
		Iterator it = nodes.iterator();
		while (it.hasNext()) {
			ASTPrimaryExpression idNode = (ASTPrimaryExpression) it.next();
			if (idNode.getVariableDecl() == fsmin.getRelatedVariable()) {
				return true;
			}
		}
		return false;
	}
	
	public static boolean checkUse(List nodes, FSMMachineInstance fsmin) {
		Iterator it = nodes.iterator();
		while (it.hasNext()) {
			SimpleNode node = (SimpleNode) it.next();
			/**add by xwt 2011.7.10*/
			if(node instanceof ASTPrimaryExpression){
				if(node.jjtGetNumChildren()!=0)
				    node = (ASTUnaryExpression) node.getFirstChildOfType(ASTUnaryExpression.class);
			}
			/**modified by xwt 2011.7.1*/
			if(node instanceof ASTUnaryExpression) {
				ASTUnaryExpression idNode = (ASTUnaryExpression) node;
                if(fsmin.getStateData() instanceof Variable) {      // post condition
                    VariableNameDeclaration varDecl = idNode.getVariableNameDeclaration();
                    if(varDecl != null) {
                        Variable var = Variable.getVariable(varDecl);
                        if(var != null && var.equals((Variable)fsmin.getStateData())) {
                            fsmin.setDesp(fsmin.getDesp() + ",在第" + idNode.getBeginLine() + "行被再次使用");
                            //fsmin.setTraceinfo(desp);
                            return true;
                        }
                    }
                } else {
                    if(idNode.getParentsOfType(ASTArgumentExpressionList.class).size() == 0 ) {	//idNode不是参数结点
                        if (idNode.getVariableDecl() == fsmin.getRelatedVariable() && fsmin.getRelatedASTNode() != idNode) {
                            //add by zhouhb
                        	//2011.3.10
                        	//修改当对p进行释放后再次进行p=NULL操作时的误报
                        	ASTAssignmentExpression assign=(ASTAssignmentExpression)idNode.getFirstParentOfType(ASTAssignmentExpression.class);
                        	if(assign!=null&&(assign.getType()instanceof CType_Pointer)){
                        		//判断当前操作是否为p=NULL操作
                        		if(assign.containsChildOfType(ASTConstant.class)&&!assign.containsParentOfType(ASTEqualityExpression.class)&&((ASTConstant)assign.getFirstChildOfType(ASTConstant.class)).getImage().equals("0")){
                        			return false;
                        		}
                        	}
                        	//end by zhouhb
                        	fsmin.setDesp(fsmin.getDesp() + "，在第" + idNode.getBeginLine() + "行再次被使用");
                            return true;
                        }
                    } else {		//变量作为实参被使用
                        String desp = checkUseInFunction(idNode);
                        if(desp != null) {
                            if (idNode.getVariableDecl() == fsmin.getRelatedVariable() && fsmin.getRelatedASTNode() != idNode) {
                                 fsmin.setDesp(fsmin.getDesp() + "，在第" + idNode.getBeginLine() + "行再次被使用");
                                 fsmin.setTraceinfo(desp);
                                return true;
                            }
                        }
                    }
                }
			} 
//			else if(node instanceof ASTqualified_id) {
//				ASTqualified_id idNode = (ASTqualified_id) node;
//				String desp = checkUseInFunction(idNode);
//				if(desp != null) {
//					if (idNode.getNameDeclaration() == fsmin.getRelatedVariable() && fsmin.getRelatedASTNode() != idNode) {
//						fsmin.setDesp(fsmin.getDesp() + "，在第" + idNode.getBeginLine() + "行再次被使用");
//						fsmin.setTraceinfo(desp);
//						return true;
//					}						
//				}
//			}
		}
		return false;
	}
	
	private static String checkUseInFunction(SimpleNode node) {
		if(node instanceof ASTUnaryExpression) {
			ASTArgumentExpressionList paramsNode = (ASTArgumentExpressionList) node.getParentsOfType(ASTArgumentExpressionList.class).get(0);
			int paramindex = -1;
			int n = paramsNode.jjtGetNumChildren();
			for(int i = 0; i < n; i++) {
				SimpleNode paramAss = (SimpleNode) paramsNode.jjtGetChild(i);
				if(paramAss.findChildrenOfType(ASTPrimaryExpression.class).size() != 0) {
					ASTUnaryExpression param = (ASTUnaryExpression) paramAss.findChildrenOfType(ASTUnaryExpression.class).get(0);
					if(param == node) {
						paramindex = i;
						break;
					}
				}
			}
			if(paramsNode.jjtGetParent() instanceof ASTPostfixExpression) {
				ASTPostfixExpression post = (ASTPostfixExpression) paramsNode.jjtGetParent();
				if(post.jjtGetNumChildren() == 2 && 
						post.jjtGetChild(0) instanceof ASTPrimaryExpression) {
					ASTPrimaryExpression funcNode = (ASTPrimaryExpression) post.jjtGetChild(0);
					if(funcNode.isMethod() && funcNode.getMethodDecl() != null) {
						MethodNameDeclaration funcDecl = (MethodNameDeclaration) funcNode.getMethodDecl();
						if(funcDecl.getMethodSummary() != null) {
							Set<MethodFeature> features = funcDecl.getMethodSummary().getPreConditions();
							for(MethodFeature feature : features) {
								if(feature instanceof MethodUFMPreCondition) {
									MethodUFMPreCondition ufmPre = (MethodUFMPreCondition) feature;
									Set<Variable> vars = ufmPre.getUFMVariables();
									for(Variable var : vars) {
										if(var.getParamIndex() == paramindex) {
											return ufmPre.getDespString(var);
										}
									}
								}
							}
						}
					}
				}
			}
		} 
//		else if(node instanceof ASTqualified_id) { 	//以qualified_id形式出现的变量使用只可能是单参函数的参数
//			ASTdeclaration decl = (ASTdeclaration) node.getParentsOfType(ASTdeclaration.class).get(0);
//			if(decl.jjtGetChild(0) instanceof ASTdeclaration_specifiers) {
//				ASTdeclaration_specifiers declsp = (ASTdeclaration_specifiers) decl.jjtGetChild(0);
//				ASTqualified_id funcNode = (ASTqualified_id) declsp.findChildrenOfType(ASTqualified_id.class).get(0);
//				if(funcNode.isMethod() && funcNode.getNameDeclaration() instanceof MethodNameDeclaration) {
//					MethodNameDeclaration funcDecl = (MethodNameDeclaration) funcNode.getNameDeclaration();
//					//free(p)中指针p不是use
//					if(!funcDecl.getName().equals("free")) {
//						//检查函数是否有对该参数的前置约束
//						if(funcDecl.getMethodSummary() != null) {
//							Set<MethodFeature> features = funcDecl.getMethodSummary().getPreConditions();
//							for(MethodFeature feature : features) {
//								if(feature instanceof MethodUFMPreCondition) {
//									MethodUFMPreCondition ufmPre = (MethodUFMPreCondition) feature;
//									Set<Variable> vars = ufmPre.getUFMVariables();
//									for(Variable var : vars) {
//										return ufmPre.getDespString(var);
//									}
//								}
//							}
//						}
//					}
//				}
//			}
//		}
		return null;
	}
	
    // 检查全局变量 类成员在函数中的使用
    public static boolean checkMethodSummary(List nodes, FSMMachineInstance fsmin) {
        Iterator it = nodes.iterator();
        while (it.hasNext()) {
            SimpleNode node = (SimpleNode) it.next();
            MethodNameDeclaration methodDecl = StateMachineUtils.getMethodNameDeclaration(node);
            if(methodDecl == null) {
                continue;
            }
            MethodSummary mtSummary = methodDecl.getMethodSummary();
            if(mtSummary == null) {
                continue;
            }
            for(MethodFeature feature : mtSummary.getPreConditions()) {
                if(feature instanceof MethodUFMPreCondition) {
                    MethodUFMPreCondition pre = (MethodUFMPreCondition) feature;
                    for(Variable ufmVar : pre.getUFMVariables()) {
                    	VariableNameDeclaration varDecl = findSingleParam(node, ufmVar);
                        if(varDecl != null && varDecl == fsmin.getRelatedVariable()) {
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }
	/**
	 * 获取当前语法树节点孩子中的所有实参节点
	 * @param node
	 * @return
	 */
	private static List<SimpleNode> getArgsNode(ASTPrimaryExpression node) {
		List<SimpleNode> argNodes = new ArrayList<SimpleNode>();
		ASTPrimaryExpression primary = null;
		ASTPostfixExpression postfix = null;
		if (node.jjtGetParent() instanceof ASTPostfixExpression) {
			primary = (ASTPrimaryExpression) node;
			postfix = (ASTPostfixExpression) node.jjtGetParent();
		} 
//		else if (node.jjtGetParent() instanceof ASTPostfixExpression) {
//			postfix = (ASTPostfixExpression) node.jjtGetParent();
//			if (postfix.jjtGetNumChildren() > 1
//					&& postfix.jjtGetChild(0) instanceof ASTPrimaryExpression) {
//				primary = (ASTPrimaryExpression) postfix.jjtGetChild(0);
//			}
//		}
		ASTArgumentExpressionList args = null;
		if (primary != null && postfix != null) {
			for (int i = 0; i < postfix.jjtGetNumChildren(); i++) {
				if (postfix.jjtGetChild(i) == primary && i + 1 < postfix.jjtGetNumChildren() && 
						postfix.jjtGetChild(i+1) instanceof ASTArgumentExpressionList) {
					args = (ASTArgumentExpressionList)postfix.jjtGetChild(i + 1);
				}
			}
		}
		if (args == null) {
			return argNodes;
		}
		for (int i = 0; i < args.jjtGetNumChildren(); i++) {
			argNodes.add((SimpleNode)args.jjtGetChild(i));
		}
		return argNodes;
	}
}
