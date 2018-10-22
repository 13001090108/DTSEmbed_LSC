package softtest.rules.c;

import softtest.fsm.c.FSMRelatedCalculation;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import softtest.ast.c.ASTAdditiveExpression;
import softtest.ast.c.ASTArgumentExpressionList;
import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTFieldId;
import softtest.ast.c.ASTFunctionDefinition;
import softtest.ast.c.ASTInitDeclarator;
import softtest.ast.c.ASTIterationStatement;
import softtest.ast.c.ASTPostfixExpression;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTSelectionStatement;
import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.CParserVisitorAdapter;
import softtest.ast.c.Node;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.Edge;
import softtest.cfg.c.VexNode;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.PointerDomain;
import softtest.domain.c.interval.PointerValue;
import softtest.fsm.c.FSMMachineInstance;
import softtest.fsm.c.FSMRelatedCalculation;
import softtest.fsm.c.FSMStateInstance;
import softtest.symboltable.c.AbstractNameDeclaration;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.Scope;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.Type.CType_AllocType;

public class AliasSet0 extends FSMRelatedCalculation
{
//	public Hashtable<VariableNameDeclaration, String> container = new Hashtable<VariableNameDeclaration, String>();
	public Hashtable<VariableNameDeclaration, ArrayList<String>> container = new Hashtable<VariableNameDeclaration, ArrayList<String>>();
	public boolean specialEmptyFlag = false;               //= false;   //false;
	
	public Object data;
	
	
	public AliasSet0()
	{
	}

	public AliasSet0(FSMRelatedCalculation o)
	{
		super(o);
		if (!(o instanceof AliasSet0))
		{
			return;
		}
		AliasSet0 t = (AliasSet0) o;
//		resourcename = t.resourcename;
		/*for (Enumeration<VariableNameDeclaration> e = t.table.elements(); e
				.hasMoreElements();)
		{
			VariableNameDeclaration v = e.nextElement();
			table.put(v, v);
		}*/
		container.putAll(t.container);
		this.specialEmptyFlag = t.specialEmptyFlag;
		this.data = t.data;
//		this.hasreturned = t.hasreturned;
//		this.isReleased = t.isReleased;
	}

	/** 拷贝 */
	@Override
	public FSMRelatedCalculation copy()
	{
		FSMRelatedCalculation r = new AliasSet0(this);
		return r;
	}
	
	public boolean isSpecialEmpty()
	{
		return this.specialEmptyFlag;
	}
	
	private void setSpecialEmpty(boolean flag)
	{
		this.specialEmptyFlag = flag;
	}
	
//	public void add(VariableNameDeclaration var, String field)
	public void add(VariableNameDeclaration var, ArrayList<String> field)
	{
		container.put(var, field);
	}
	
	public void add(VariableNameDeclaration var)
	{
		container.put(var, null);
	}
	
//	public void addAll(Map<VariableNameDeclaration, String> vars)
	public void addAll(Map<VariableNameDeclaration, ArrayList<String>> vars)
	{
		container.putAll(vars);
	}
	
	public boolean containsVar(VariableNameDeclaration var)
	{
		return container.containsKey(var);
	}
	
	public boolean isEmpty()
	{
		return container.isEmpty();
	}
	
	public void remove(VariableNameDeclaration var)
	{
		container.remove(var);
	}
	
//	public String getField(VariableNameDeclaration var)
	public ArrayList<String> getField(VariableNameDeclaration var)
	{
		return container.get(var);
	}
	
	public Enumeration<VariableNameDeclaration> Vars()
	{
		return container.keys();
	}
	
	
	public void calculateIN(FSMMachineInstance fsmin, VexNode vex, Object data)
	{
		/**第0步 一些判断*/
		
		/**第1步*/
		List<Edge> edges = new ArrayList<Edge>();
		Enumeration<Edge> en1 = vex.getInedges().elements();
		while(en1.hasMoreElements())
		{
			Edge e = en1.nextElement();
			edges.add(e);
		}
		Collections.sort(edges);
		
		/**第2步*/
		//合并时 注意specialEmptyFlag的值
		//怎么体现出来只有alloc状态下AliasSet才合并————我的理解是aliasSet真正应该是和alloc状态关联   但是目前aliasSet是与fsmin关联 而不是状态   而一个fsmin可能包含多个状态
		boolean specialFlag = true;
		boolean hasChanged = false;
		for(Edge e : edges)
		{
			if(e.getContradict())
			{
				continue;
			}
			
			VexNode pre = e.getTailNode();
			if(pre.getFSMMachineInstanceSet() != null)
			{
				FSMMachineInstance prefsmin = pre.getFSMMachineInstanceSet().getTable().get(fsmin);
				if(prefsmin != null)
				{
					Enumeration<FSMStateInstance> en2 = prefsmin.getStates().getTable().elements();
					while(en2.hasMoreElements())
					{
						FSMStateInstance statein = (FSMStateInstance)en2.nextElement();
						if(statein.getState().getName().equals("CALLOC"))
						{
							AliasSet0 preAlias = (AliasSet0)prefsmin.getRelatedObject();
							this.addAll(preAlias.container);
							specialFlag = specialFlag && preAlias.specialEmptyFlag;
							hasChanged = true;
							
							break;
						}
					}
						
				}
				
			}
		}
		
		if(hasChanged)
		{
			this.specialEmptyFlag = specialFlag;
		}
		
	}
	
	
	public void calculateOUT(FSMMachineInstance fsmin, VexNode vex, Object data)
	{
		
		/**第0步 一些判断*/
		
		//不加以下几行(至if(!hasCalloc)return) test-team-1::1用例就会通不过 因为specialEmptyFlag 赋值错误
		boolean hasCalloc = false;
		Enumeration<FSMStateInstance> en0 = fsmin.getStates().getTable().elements();
		while(en0.hasMoreElements())
		{
			FSMStateInstance statein = (FSMStateInstance)en0.nextElement();
			if(statein.getState().getName().equals("CALLOC"))
			{
				hasCalloc = true;
				break;
			}
			
		}
		if(!hasCalloc)
		{
			return;
		}

		/**第一步 去除空指针*/
//		setSpecialEmpty(false);                                            //不能在开始处给SpecialEmptyFlag赋值为false 在不同分支AliasSet合并时SpecialEmptyFlag才可能从true变为false, 两个分支SpecialEmptyFlag合并时取&???
		vex.setfsmCompute(true);
		Enumeration<VariableNameDeclaration> en1 = Vars();
		while(en1.hasMoreElements())
		{
			VariableNameDeclaration var = en1.nextElement();
			
			/*if(! (vex.getDomain(var) instanceof PointerDomain))
			{
				System.err.println("出错了 AliasSet0 ：： calculateOUT");
				System.err.println(vex.getTreenode().getFileName());
				System.err.println(vex.getTreenode().getBeginLine() + "      " + vex.getTreenode().getBeginFileLine());
				System.err.println(vex.getName());
				System.err.println(var.getImage());
			}*/
			/*Domain lastDomain = vex.getDomain(var);
			PointerDomain pld = (PointerDomain)vex.getDomain(var);                        //这里直接类型转换而不在之前做判断 是因为AliasSet中保存的都是指针变量  如果这里报异常 只能说明变量加入AliasSet处理有问题 让非指针变量加入了AliasSet
			if(pld != null && pld.getValue() == PointerValue.NULL && pld.offsetRange == null)                       //是不是还要判断offrange是empty的情况
			{
				remove(var);
			}*/
			if(vex.getDomain(var) != null && vex.getDomain(var) instanceof PointerDomain)
			{
				PointerDomain pld = (PointerDomain)vex.getDomain(var);
				if(pld.getValue() == PointerValue.NULL|| !pld.Type.contains(CType_AllocType.heapType))
				{
					remove(var);
				}
			}
		}
		vex.setfsmCompute(false);
		
		if(isEmpty())                                 //这是不是还要加上判断之前不为空呢      不用了吧      如果之前就为空了 那么在之前就已经报memoryLeak了
		{
//			if(vex.getInedges().size() == 1)
			{
//				String tail = vex.getInedges().keys().nextElement();
				
				Enumeration<Edge> en = vex.getInedges().elements();
				while(en.hasMoreElements())
				{
					VexNode pre = en.nextElement().getTailNode();
					if(pre.getName().indexOf("if_head") != -1)                             //还用考虑while_head 和 for_head么
					{
						setSpecialEmpty(true);
					}
				}
				
				/*VexNode pre = vex.getInedges().elements().nextElement().getTailNode();
				if(pre.getName().indexOf("if_head") != -1)                             //还用考虑while_head 和 for_head么
				{
					setSpecialEmpty(true);
				}*/
			}
			
			return;
		}
		
		
		/**第二步 考察赋值表达式、++/--等 ———— 通过visitor*/
		SimpleNode curTreeNode = vex.getTreenode();
		/*Visitor visitor = new Visitor();
		VisitData vd  = new VisitData(); */                                                                 //这样不好 每一次遍历控制流图的结点 就要新生成一次这两个对象
		Visitor visitor = Visitor.getInstance();
		VisitData vd = VisitData.getInstance(container);
		curTreeNode.jjtAccept(visitor, vd);
		vd.reset();
		
		
		/**第三步 去除超出作用域的指针变量*/                                                      //这步貌似可以合并在第二步中的visitor中
		Scope curScope = curTreeNode.getScope();
		Enumeration<VariableNameDeclaration> en3 = Vars();
		while(en3.hasMoreElements())
		{
			VariableNameDeclaration var = en3.nextElement();
			Scope varScope = var.getScope();
			if(!curScope.isSelfOrAncestor(varScope))
			{
				remove(var);
			}
		}
		

		
	}
	
	
	
	static class Visitor extends CParserVisitorAdapter                                                 //因为Java中不允许多重继承 我才写成内部类的 
	{
		private static Visitor instance;
		
		static Visitor getInstance()
		{
			if(instance == null)
			{
				instance = new Visitor();
			}
			
			return instance;
		}
		
		
		public Object visit(ASTUnaryExpression node, Object data)
		{
			if( !(data instanceof VisitData))
			{
				return null;
			}
			VisitData vd = (VisitData)data;
			
			int sn = vd.vlist.size();
			super.visit(node, vd);
			int en = vd.vlist.size() - sn;
			
			if(en == 1)                                         //？？？ en > 0
			{
				if("++".equals(node.getOperators()) || "--".equals(node.getOperators()))
				{
					if(vd.vlist.get(0) instanceof VariableNameDeclaration)
					{
						VariableNameDeclaration var = (VariableNameDeclaration)vd.vlist.get(0);
						
						ArrayList<String> field = vd.field;
						
						if(vd.alias.containsKey(var))
						{
							ArrayList<String> vf = vd.alias.get(var);
							boolean flag = vf.size() == field.size();
							for(int i=0; i<vf.size()&&flag; i++)
							{
								if(!vf.get(i).equals(field.get(i)))
								{
									flag = false;
								}
							}
							
							if(flag)
							{
								vd.alias.remove(var);
							}
						}
						
						/*if(vd.alias.containsKey(var))
						{
							vd.alias.remove(var);
						}*/
					}
				}
			}
			
			return null;
		}
		
		public Object visit(ASTPostfixExpression node, Object data)
		{
			if( !(data instanceof VisitData))
			{
				return null;
			}
			VisitData vd = (VisitData)data;
			
			int sn = vd.vlist.size();
			super.visit(node, vd);
			int en = vd.vlist.size() - sn;
			
			if(en == 1)                                                            //？？？en > 0
			{
				if("++".equals(node.getOperators()) || "--".equals(node.getOperators()))
				{
					if(vd.vlist.get(0) instanceof VariableNameDeclaration)
					{
						VariableNameDeclaration var = (VariableNameDeclaration)vd.vlist.get(0);
						
						ArrayList<String> field = vd.field;
						
						if(vd.alias.containsKey(var))
						{
							ArrayList<String> vf = vd.alias.get(var);
							boolean flag = vf.size() == field.size();
							for(int i=0; i<vf.size()&&flag; i++)
							{
								if(!vf.get(i).equals(field.get(i)))
								{
									flag = false;
								}
							}
							
							if(flag)
							{
								vd.alias.remove(var);
							}
						}
					}
				}
			}
			
			return null;
		}
		
		public Object visit(ASTAssignmentExpression node, Object data)
		{
			
			if( !(data instanceof VisitData))
			{
				return null;
			}
			VisitData vd = (VisitData)data;
			
			Node left = node;
			Node right = null;
			
			if(node.jjtGetNumChildren() == 3)
			{
				SimpleNode operator = (SimpleNode)node.jjtGetChild(1);
				if("=".equals(operator.getOperators()))
				{                                                                              //已修改   实际中那种情况也不多见   可能产生误差
//					left = (ASTUnaryExpression)node.jjtGetChild(0);//其实在这里 left的实际类型应该是unaryExpression 在这里我处理成SimpleNode了 对++i=j的情况 左边就不会遍历一元表达式++i 而直接去遍历一元表达式的子节点
					left = node.jjtGetChild(0);
//					right = (ASTAssignmentExpression)node.jjtGetChild(2);
					right = node.jjtGetChild(2);
				}
			}
			
			if(right == null)
			{
				super.visit((SimpleNode)left, vd);
			}
			
			if(right != null)
			{
				
				int sn = vd.vlist.size();
				left.jjtAccept(this, vd);
				int en1 = vd.vlist.size();
															
				if(en1-sn == 1)                              
				{
					Object obj = vd.vlist.get(0);
					if(! (obj instanceof VariableNameDeclaration))
					/*
					 * extern int *	__errno(void);
					 * static int hpcfsErrnoMap(int);
					 * ......
					 * (*__errno()) = 0;
					 * (*__errno()) = hpcfsErrnoMap(result);
					 * 
					 * 这样以来赋值表达式左侧取到的就是methodNameDeclaration了 暂时只是屏蔽 不处理这种问题
					 */
					{
						return null;
					}
						
					VariableNameDeclaration lv = (VariableNameDeclaration)obj;
					
//					VariableNameDeclaration lv = (VariableNameDeclaration)vd.vlist.get(0);                             //赋值表达式左面不可能是method/class吧
//					String lf = vd.field;
					ArrayList<String> lf = (ArrayList<String>)vd.field.clone();
//					vd.field = "NULL";
					vd.field.clear();
					if(right != null)
					{
						right.jjtAccept(this, vd);
						int en2 = vd.vlist.size();
						if(en2-en1 == 1)
						{
							AbstractNameDeclaration r = vd.vlist.get(0);
//							String rf = vd.field;
							ArrayList<String> rf = (ArrayList<String>)vd.field.clone();
//							vd.field = "NULL";
							vd.field.clear();
							if(r instanceof VariableNameDeclaration)
							{
								VariableNameDeclaration rv = (VariableNameDeclaration)r;
								
								if(vd.alias.containsKey(rv))
								{
									vd.alias.put(lv, lf);
								}
								else
								{
//									***************************
//									if(vd.alias.containsKey(lv) && vd.alias.get(lv).equals(lf) && rv.getType().equalType(lv.getType()))  //2010-10-26 加最后的这个条件 为了处理 a[1] = b
									if(vd.alias.containsKey(lv))
									{
										ArrayList<String> field = vd.alias.get(lv);
										boolean flag = field.size() == lf.size();
										for(int i=0; i<field.size() && flag; i++)
										{
											if(!field.get(i).equals(lf.get(i)))
											{
												flag = false;
											}
										}
										if(flag)
										{
											vd.alias.remove(lv);
										}
									}
								}
							}
							else
								if(r instanceof MethodNameDeclaration && r.getImage().indexOf("realloc") == -1)
								{
									if(vd.alias.containsKey(lv) && vd.alias.get(lv).equals(lf))
									{
										vd.alias.remove(lv);
									}
								}
						}
						
					}
				}
			}
			
			return null;
		}
		
		public Object visit(ASTInitDeclarator node, Object data)
		{
			return null;
		}
		
		public Object visit(ASTPrimaryExpression node, Object data)
		{
			if( !(data instanceof VisitData))
			{
				return null;
			}
			VisitData vd = (VisitData)data;
			
			super.visit(node, vd);
			
			if(node.getVariableDecl() != null)
			{
				VariableNameDeclaration varDecl = node.getVariableDecl();
				vd.vlist.add(0, varDecl);
				
				//2010-10-26
				/*if(node.getNextSibling() != null)
				{
					if(node.getNextSibling() instanceof ASTFieldId)
					{
						ASTFieldId sibling = (ASTFieldId)node.getNextSibling();
						vd.field = sibling.getImage();
					}
					else
					{
						vd.field = "unkown";
					}
				}*/
				
				SimpleNode sn = (SimpleNode)node.getNextSibling();
				while( sn!= null)
				{
					if(sn instanceof ASTFieldId)
					{
						ASTFieldId sibling = (ASTFieldId)sn;
						vd.field.add(sibling.getImage());
					}
					else
					{
						vd.field.add("unkown");
					}
					
					sn = (SimpleNode)sn.getNextSibling();
				}
				
			}
			else
				if(node.getMethodDecl() != null)
				{
					MethodNameDeclaration methodDecl = node.getMethodDecl();
					vd.vlist.add(0, methodDecl);
				}
			
			/*if(node.getNextSibling() != null && node.getNextSibling() instanceof ASTFieldId)
			{
				ASTFieldId sibling = (ASTFieldId)node.getNextSibling();
//				vd.field = sibling.getVariableNameDeclaration();
				vd.field = sibling.getImage();
			}*/
			
			return null;
		}
		
		public Object visit(ASTAdditiveExpression node, Object data)                                    //？？？该不该屏蔽加法表达式呢
		{
			return null;
		}
		
		public Object visit(ASTArgumentExpressionList node, Object data)
		{
			return null;
		}
		
		public Object visit(ASTSelectionStatement node, Object data)
		{
			return null;
		}
		public Object visit(ASTIterationStatement node, Object data)
		{
			return null;
		}
		public Object visit(ASTFunctionDefinition node, Object data)
		{
			return null;
		}
	}
	
	static class VisitData
	{
		private static VisitData instance;
		
//		static VisitData getInstance(Hashtable<VariableNameDeclaration, String> a)
		static VisitData getInstance(Hashtable<VariableNameDeclaration, ArrayList<String>> a)
		{
			if(instance == null)
			{
				instance = new VisitData();
			}
			
			instance.setAliasSet(a);
			
			return instance;
		}
		
//		private void setAliasSet(Hashtable<VariableNameDeclaration, String> a)
		private void setAliasSet(Hashtable<VariableNameDeclaration, ArrayList<String>> a)
		{
			alias = a;
		}
		
//		Hashtable<VariableNameDeclaration, String>alias = null;
		Hashtable<VariableNameDeclaration, ArrayList<String>>alias = null;
		List<AbstractNameDeclaration> vlist = new LinkedList<AbstractNameDeclaration>();
//		String field = "NULL";
		ArrayList<String> field = new ArrayList<String>();		
		void reset()
		{
			vlist.clear();
//			field = "NULL";
			field.clear();
			alias = null;
		}
	}
}
