package softtest.scvp.c;

import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Queue;

import javax.xml.transform.Source;

import java.util.LinkedList;
import java.util.List;

import softtest.domain.c.symbolic.Expression;
import softtest.ast.c.ASTAdditiveExpression;
import softtest.ast.c.ASTArgumentExpressionList;
import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTConstant;
import softtest.ast.c.ASTDirectDeclarator;
import softtest.ast.c.ASTExclusiveORExpression;
import softtest.ast.c.ASTFunctionDefinition;
import softtest.ast.c.ASTInclusiveORExpression;
import softtest.ast.c.ASTMultiplicativeExpression;
import softtest.ast.c.ASTParameterList;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.AbstractExpression;
import softtest.ast.c.Node;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.Edge;
import softtest.cfg.c.Graph;
import softtest.cfg.c.GraphVisitor;
import softtest.cfg.c.VexNode;
import softtest.interpro.c.Method;
import softtest.symboltable.c.LocalScope;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.NameDeclaration;
import softtest.symboltable.c.NameOccurrence;
import softtest.symboltable.c.Search;
import softtest.symboltable.c.SourceFileScope;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.NameOccurrence.OccurrenceType;
import softtest.symboltable.c.Type.CType_Pointer;

public class SideEffectsVisitor implements GraphVisitor{
	HashSet<NameOccurrence> effectVars = new HashSet<NameOccurrence>();
	private Method method;
	public void visit(VexNode n, Object data) {
		// TODO Auto-generated method stub
		//System.out.println(n.getValueSet());
		
		if(n.getName().startsWith("func_head")) { //函数入口节点，记录下所有传入的指针参数
			ASTFunctionDefinition methodNode = (ASTFunctionDefinition)n.getTreenode();
			method = methodNode.getDecl().getMethod();
			for(NameOccurrence occ:n.getOccurrences()) {
				if(occ.getDeclaration().getType() instanceof CType_Pointer) {
					//effectVars.add(occ.getDeclaration());
					effectVars.add(occ);
				}
					
			}
			//System.out.println("effectVars="+effectVars);
		}
		
		else if(n.getName().startsWith("return") || n.getName().startsWith("func_out")) {
			HashMap<Integer,Boolean> visited = new HashMap<Integer, Boolean>();
			if(n.getName().startsWith("return")) {
				SimpleNode returnNode = n.getTreenode();
				List<Node> constList = returnNode.findChildrenOfType(ASTConstant.class);
				List<Node> varList = returnNode.findLeafChildrenOfType(ASTPrimaryExpression.class);
				String funcs = "";
				for(Node var:varList) {
					if(((ASTPrimaryExpression)var).isMethod()) {
						funcs+="Function:"+((ASTPrimaryExpression)var).getImage();
						String temp = ((ASTPrimaryExpression)var).getImage();
					}
					if(((SimpleNode)var).isLeaf()==false)
						varList.remove(var);
				}
				SCVP value = new SCVP();
				if(constList.size()==1 && varList.size()==0){ //仅有一个常数
					value.setStructure("return constant");
					value.setConstants(constList);  
					value.setPosition(new Position(n, returnNode));
				}
				else if(constList.size()==0 && varList.size()==1) { //仅有一个变量
					if(((ASTPrimaryExpression) varList.get(0)).isMethod()==false) {
						value.setStructure("return variable");
						for(NameOccurrence occ:n.getOccurrences())
							value.getOccs().add(occ);
						value.setPosition(new Position(n, returnNode));
					}
					else {
						value.setStructure(funcs);
						value.setPosition(new Position(n, returnNode));
					}
				}
				else if(constList.size()==0 && varList.size()==0) { //返回空值
					value.setStructure("return nothing");
					value.setPosition(new Position(n, returnNode));
				}
				else { //返回表达式
					List<Node> nodes = returnNode.findChildOfTypes(new Class[]{
							ASTAdditiveExpression.class,//+ -
							ASTMultiplicativeExpression.class,//* /
							ASTInclusiveORExpression.class,//&|
							ASTExclusiveORExpression.class//^
							});//枚举所有有操作符的ast节点，有待添加
					String structure="";
					for(Node node:nodes) {
						structure+="Operator:"+((SimpleNode)node).getOperators().replace(" ", "");
					}
					structure+=funcs;
					value.setStructure(structure);
					value.setConstants(constList);
					for(NameOccurrence occ:n.getOccurrences())
						value.getOccs().add(occ);
					value.setPosition(new Position(n, returnNode));
				}
				//method.getReturnList().add(value);
				method.getReturnList().add(value.convertToString());
				//value.printSCVP();
			}
			for(NameDeclaration decl : n.getValueSet().getTable().keySet()) {
				//added by cmershen,2016.6.6
				//处理全局信息
				ArrayList<NameOccurrence> list = n.getLiveDefs().getVariableLiveDefs((VariableNameDeclaration) decl);
				if(list!=null) {
					for(NameOccurrence occ:list) {
						if(occ.getDeclaration().getScope().getClass().equals(LocalScope.class)==false)//本地变量不加入后置摘要
							method.getExternalEffects().put(occ.toString(), occ.scvpList);	
					}
				}
				for(NameOccurrence occ:effectVars) {
					if(occ.getDeclaration().equals(decl)) {
						//add by cmershen,2016.5.30
						//寻找decl的最后一次出现,因为decl是指针，要找decl所指符号的变化，这里使用图的广度优先遍历(BFS)
						//管你什么算法，我就是喜欢for循环！！！
						String str = decl.getImage();
						Expression exp = null;
						NameDeclaration newdecl = null;
						for(NameDeclaration decl2:n.getValueSet().getTable().keySet()) {
							if(decl2.getImage().equals("*"+str)) {
								//System.out.println(decl2);
								exp = n.getValue((VariableNameDeclaration) decl2);
								newdecl = decl2;
								break;
							}
						}
						//System.out.println("Node=" + n + " Value="+exp);
						//System.out.println("Starting BFS...");
						//System.out.println(exp);
						Queue<VexNode> q = new LinkedList<VexNode>();
						q.offer(n);
						visited.put(n.getSnumber(), true);
						VexNode node=null,lastnode = node;
						while(!q.isEmpty()) {
							lastnode = node;
							node = q.poll();
							visited.put(node.getSnumber(), true);
							//System.out.println(node);
							if(!node.equals(n)) {
								if(lastnode==null || lastnode.getValueSet()==null || newdecl==null)
									break;
								Expression lastexp = lastnode.getValueSet().getValue((VariableNameDeclaration) newdecl);
								Expression exp2 = node.getValueSet().getValue((VariableNameDeclaration) newdecl);
								if(exp2!=null) {
									if(!exp2.equals(exp)) {
										//System.out.println("Node=" + node + " Value="+exp2 + ",lastnode=" + lastnode + " last value="+lastexp);
										//lastnode就是定义点
										NameOccurrence key = null;
										for(NameOccurrence occ2:lastnode.getOccurrences()) {
											if(occ2.getImage().equals(decl.getImage())) {
												key = occ2;
												break;
											}
										}	
										if(key!=null) {
											List<SCVPString> value = key.scvpList;
											method.getExternalEffects().put(key.toString(), value);
											
										}
									}
								}
							}
							for(Edge e:node.getInedges().values()) {
								if(!visited.containsKey(e.getTailNode().getSnumber()))
									q.offer(e.getTailNode());
							}
							
						}
					}
				}
				//System.out.println(method+method.getExternalEffects().toString());
			}
		}
		else { // 寻找函数调用点   added by cmershen 2016.7.4
			
			List<Node> list = n.getTreenode().findChildrenOfType(ASTPrimaryExpression.class);
			if(list.size()!=0) {
				//ASTPrimaryExpression node = (ASTPrimaryExpression)(list.get(0));
				for(Node nd:list) {
					//modified by cmershen,2016.12.14 修正一下，因为函数调用节点有可能不是第一个PrimaryExpression.
					if(nd instanceof ASTPrimaryExpression) {
						ASTPrimaryExpression node = (ASTPrimaryExpression)nd;
						if(node.isMethod()) { //节点本身是函数调用
							//added by cmershen,2016.10.20
							//如果有调用的函数有函数副作用，传到当前函数的副作用里面。
							try{
								method.getExternalEffects().putAll(node.getMethodDecl().getMethod().getExternalEffects());
								//System.out.println(method+method.getExternalEffects().toString());

							}
							catch(NullPointerException e) {
								
							}
							//added by cmershen,2016.11.4 前置摘要增加受影响的全局信息
		
							ASTArgumentExpressionList astnode = (ASTArgumentExpressionList) ((SimpleNode)(node.jjtGetParent())).getFirstDirectChildOfType(ASTArgumentExpressionList.class);
							
							for(NameOccurrence occ:n.getLiveDefs().getOccs()) {
								if(occ.getOccurrenceType() == OccurrenceType.DEF || occ.getOccurrenceType() == OccurrenceType.DEF_AFTER_USE) {
									if(occ.getDeclaration().getScope() instanceof SourceFileScope) {
										ArrayList<SCVPString> list2 = new ArrayList<SCVPString>();
										try {
											list2.add(occ.scvpList.get(0));
											Position p = null;
											if (astnode != null)
												p = new Position(n,astnode);
											else 
												p = new Position(n,occ);
											node.getMethodDecl().getMethod().getCallerInfo().put(p, list2);
										} catch (Exception e) {
											// TODO Auto-generated catch block
										}
										
										
									}
								}
							}
							
							for(NameOccurrence occ:n.getOccurrences()) {
								if(occ.getLocation().containsParentOfType(ASTArgumentExpressionList.class) && occ.getLocation().getFirstParentOfType(ASTArgumentExpressionList.class).equals(astnode)) {
									if(occ.getUse_def()!=null && occ.getUse_def().size()>0) {
										NameOccurrence def = occ.getUse_def().get(0);
										if(def.scvpList.size()>0) {
											//Position key = def.scvpList.get(0).getPosition();
											Position key2 = new Position(n, astnode);
											ArrayList<SCVPString> value = (ArrayList<SCVPString>)def.scvpList;
											if(node!=null && node.getMethodDecl()!=null && node.getMethodDecl().getMethod()!=null) {
												SimpleNode occNode = (SimpleNode) occ.getLocation().getFirstParentOfType(ASTAssignmentExpression.class);
												int index = occNode.getIndexOfParent() + 1;
												key2.setFunction(true);
												key2.setIndex(index);
												node.getMethodDecl().getMethod().getCallerInfo().put(key2, value);
											}
											
											if(node.getMethodDecl()==null) {
												SimpleNode root = (SimpleNode) node.getFirstParentOfType(ASTTranslationUnit.class);
												SourceFileScope scope = (SourceFileScope) root.getScope();
												NameDeclaration decl = Search.searchInAllUpward(node.getImage(), scope);
												if(decl!=null && decl instanceof MethodNameDeclaration) {
													MethodNameDeclaration mDecl = (MethodNameDeclaration) decl;
													Method m = mDecl.getMethod();
													SimpleNode occNode = (SimpleNode) occ.getLocation().getFirstParentOfType(ASTAssignmentExpression.class);
													int index = occNode.getIndexOfParent() + 1;
													key2.setFunction(true);
													key2.setIndex(index);
													m.getCallerInfo().put(key2, value);
												}
											}
										}
									}
								}	
							}
//							if(node.getMethodDecl()!=null)
//								System.out.println(node.getImage()+":"+node.getMethodDecl().getMethod().getCallerInfo());
						}
					}
				}
			}

		}
	}

	public void visit(Edge e, Object data) {
		// TODO Auto-generated method stub
		
	}

	public void visit(Graph g, Object data) {
		// TODO Auto-generated method stub
		
	}
	
	public void dump() throws IOException {
		FileWriter fw = new FileWriter("E:\\测试用例\\du_statistics.txt", true);
		
		//System.out.println(method.getExternalEffects());
		if(method.getExternalEffects().size()!=0)
			fw.append("ExternalEffects:"+method.getName()+"\n");
		//System.out.println(method.getCallerInfo());
		if(method.getCallerInfo().size()!=0)
			fw.append("CallerInfo:"+method.getName()+"\n");
		fw.close();
		
	}
}
