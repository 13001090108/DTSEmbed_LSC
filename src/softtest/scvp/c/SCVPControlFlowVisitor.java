package softtest.scvp.c;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

import softtest.ast.c.ASTAdditiveExpression;
import softtest.ast.c.ASTConstant;
import softtest.ast.c.ASTDirectDeclarator;
import softtest.ast.c.ASTExclusiveORExpression;
import softtest.ast.c.ASTFieldId;
import softtest.ast.c.ASTInclusiveORExpression;
import softtest.ast.c.ASTMultiplicativeExpression;
import softtest.ast.c.ASTParameterList;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTStatement;
import softtest.ast.c.Node;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.Edge;
import softtest.cfg.c.Graph;
import softtest.cfg.c.GraphVisitor;
import softtest.cfg.c.VexNode;
import softtest.domain.c.analysis.VarDomainSet;
import softtest.symboltable.c.NameOccurrence;
import softtest.symboltable.c.NameOccurrence.DefinitionType;
import softtest.symboltable.c.NameOccurrence.OccurrenceType;

public class SCVPControlFlowVisitor implements GraphVisitor {

	public void visit(VexNode n, Object data) {
		// added by cmershen,2016.5.3
		List<NameOccurrence> occs = n.getOccurrences();
		
		if(n.getName().startsWith("func_head")) {
			// 对函数入口节点开始分析
			for(NameOccurrence occ:occs) {
				if(occ.getOccurrenceType()==OccurrenceType.ENTRANCE) {
					SCVP scvp = new SCVP();
					scvp.setOcc(occ);
					//S
					//added by cmershen,2016.10.17增加入口参数的索引号
					
					try {
						SimpleNode entNode = (SimpleNode) n.getTreenode().getFirstChildOfType(ASTParameterList.class);
						List<Node> paraList = entNode.findChildrenOfType(ASTDirectDeclarator.class);
						int index = 0;
						for (int i = 1; i <= paraList.size(); i++) {
							SimpleNode paraNode = (SimpleNode) paraList.get(i - 1);
							if (paraNode.getImage().equals(occ.getImage()))
								index = i;
						}
						scvp.setStructure("entrance of function,index:" + index);
					} catch (Exception e) {
						// TODO: handle exception
					}
					//C
					scvp.setConstants(null);//c语言中没有默认赋值，但C++和java中有，例如void f(int i=1)是可以的
					//V
					//List<SimpleNode> variables= new ArrayList<SimpleNode>();
					HashSet<NameOccurrence> occs1 = new HashSet<NameOccurrence>();
					
					occs1.add(occ);
					//variables.add(occ.getLocation());
					
					//scvp.setVariables(variables);
					scvp.setOccs(occs1);
					//P			
					Position p=new Position(n,occ);
					scvp.setPosition(p);
					//dump
					//scvp.printSCVP();
					occ.scvpList.add(scvp.convertToString());//changed by cmershen
				}
			}
		}
		else {
			for(NameOccurrence occ:occs) {
				if(occ.getOccurrenceType()==OccurrenceType.DEF || occ.getOccurrenceType()==OccurrenceType.DEF_AFTER_USE) {
					
					SCVP scvp = new SCVP();
					scvp.setOcc(occ);
					//S
					SimpleNode astnode = (SimpleNode) occ.getLocation().getFirstParentOfType(ASTStatement.class);
					List<Node> nodes = astnode.findChildOfTypes(new Class[]{
							ASTAdditiveExpression.class,//+ -
							ASTMultiplicativeExpression.class,//* /
							ASTInclusiveORExpression.class,//&|
							ASTExclusiveORExpression.class//^
							});//枚举所有有操作符的ast节点，有待添加
					String structure="";
					if(occ.definitionType==DefinitionType.CONDITION) {
						//VarDomainSet set = n.getVarDomainSet();
						structure+="Condition:";//+set.toString();
					}
					else if(occ.definitionType==DefinitionType.LOOP) {
					//	VarDomainSet set = n.getVarDomainSet();
						structure+="Loop:";//+set.toString();
					}
					else if(occ.definitionType==DefinitionType.LIB) {
						System.out.println(occ.getLocation());
						structure+="Lib Function:";
					}
					for(Node node:nodes) {
						structure+="Operator:"+((SimpleNode)node).getOperators().replace(" ", "");
					}
					
					scvp.setStructure(structure);
					//C
					List<Node> constants=astnode.findChildrenOfType(ASTConstant.class);
					scvp.setConstants(constants);
					//V
					List<Node> temp=astnode.findChildOfTypes(new Class[]{ASTPrimaryExpression.class,ASTFieldId.class});
					//List<SimpleNode> variables = new LinkedList<SimpleNode>();
					HashSet<NameOccurrence> occs2 = new HashSet<NameOccurrence>();
					for(Node node:temp) {
						if(((SimpleNode)node).getImage().equals(occ.getImage())==false) {
							if(((SimpleNode)node).isLeaf())  {
								if(node instanceof ASTPrimaryExpression) {
									if(((ASTPrimaryExpression)node).isMethod()==false) {
										for(NameOccurrence occ2:n.getOccurrences()) {
											if(occ2.getOccurrenceType()==OccurrenceType.USE) {
												occs2.add(occ2);
												
											}
										}
									}
									else {
										structure+="Function:"+((ASTPrimaryExpression)node).getImage();
										scvp.setStructure(structure);
									}
								}
								else if(node instanceof ASTFieldId) {
									//variables.add((SimpleNode) node);
									for(NameOccurrence occ2:n.getOccurrences()) {
										if(occ2.getOccurrenceType()==OccurrenceType.USE) {
											occs2.add(occ2);
										}

									}
								}
							}
						}
					}
					
					
					//scvp.setVariables(variables);
					scvp.setOccs(occs2);
					for (NameOccurrence occ2 : occs2) {
						occ2.getEffected().add(occ);
					}
					//P
					Position p=new Position(n,occ);
					scvp.setPosition(p);
					//dump
				//	scvp.printSCVP();
				//	scvp.printSCVPtoFile("E:\\julei\\sphinxbase.txt");
					occ.scvpList.add(scvp.convertToString());//changed by cmershen
					
				}
				else {
					regenerateDU(occ,n);//重构定义使用链，寻找occ的定义点
				}
			}
		}

	}



	@SuppressWarnings("unused")
	private void regenerateDU(NameOccurrence occ,VexNode vNode) {
		// using bfs to find definition of occ
		//vNode stands for the location of occ
		HashSet<Integer> visited = new HashSet<Integer>();
		visited.add(vNode.getSnumber());
		
		Queue<VexNode> q = new LinkedList<VexNode>();
		for(Edge e:vNode.getInedges().values()) {
			if(!visited.contains(e.getTailNode().getSnumber())) {
				q.offer(e.getTailNode());
				visited.add(e.getTailNode().getSnumber());
			}
		}
		VexNode cur = null;
		while(!q.isEmpty()) {
			cur = q.poll();
			visited.add(cur.getSnumber());
			//cur是函数调用点且有对occ的副作用
			List<Node> list = cur.getTreenode().findChildrenOfType(ASTPrimaryExpression.class);
			if(list.size()!=0) {
				ASTPrimaryExpression node = (ASTPrimaryExpression)(list.get(0));
				if(node.isMethod()) { //节点本身是函数调用
					if(node.getImage().equals("malloc")) {
						occ.addUseDef(new NameOccurrence(null, node, "malloc"));
						break;
					}
					if(node.getMethodDecl()==null)
						break;
					HashMap<String, List<SCVPString>> externalEffects = node.getMethodDecl().getMethod().getExternalEffects();
					if(!externalEffects.isEmpty()) {
						for(String key:externalEffects.keySet()) {
							if(key.split(":")[0].equals(occ.getImage())) {
								//vNode的定义点在node点，occ的定义点是key
								occ.getUse_def().clear();
								//occ.addUseDef(new N);
								
							}
						}
					}
				}
			}
			for(Edge e:cur.getInedges().values()) {
				if(!visited.contains(e.getTailNode().getSnumber())) {
					q.offer(e.getTailNode());
					visited.add(e.getTailNode().getSnumber());
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
}
