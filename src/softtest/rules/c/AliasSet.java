package softtest.rules.c;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;


import softtest.ast.c.*;
import softtest.cfg.c.Edge;
import softtest.cfg.c.VexNode;
import softtest.fsm.c.FSMMachineInstance;
import softtest.fsm.c.FSMRelatedCalculation;
import softtest.interpro.c.Variable;
import softtest.rules.c.AliasSet;
import softtest.rules.c.StateMachineUtils;
import softtest.rules.gcc.fault.MLFStateMachine;
import softtest.rules.gcc.fault.MLFStateMachine.CheckType;
import softtest.summary.c.MMFetureType;
import softtest.summary.gcc.fault.MethodMMFeature;
import softtest.summary.c.MethodSummary;
import softtest.symboltable.c.*;
import softtest.symboltable.c.Type.CType_Pointer;
import softtest.symboltable.c.ClassScope;
import softtest.symboltable.c.Scope;
import softtest.symboltable.c.VariableNameDeclaration;

public class AliasSet extends FSMRelatedCalculation
{
	private String resourcename = "";

	/** 函数返回了别名集合元素标志 */
	private boolean hasreturned = false;

	private boolean isReleased = true;
	
	private boolean forLoop = false;
	
	public void setforLoop(boolean forLoop) {
		this.forLoop = forLoop;
	}
	public boolean IsForLoop() {
		return forLoop;
	}

	public void setIsReleased(boolean isReleased)
	{
		this.isReleased = isReleased;
	}

	public boolean isReleased()
	{
		return isReleased;
	}

	/** 设置函数返回了别名集合元素标志 */
	public void setHasReturned(boolean hasreturned)
	{
		this.hasreturned = hasreturned;
	}

	/** 获取函数返回了别名集合元素标志 */
	public boolean getHasReturned()
	{
		return hasreturned;
	}

	public AliasSet()
	{
	}

	public AliasSet(FSMRelatedCalculation o)
	{
		super(o);
		if (!(o instanceof AliasSet))
		{
			return;
		}
		AliasSet t = (AliasSet) o;
		resourcename = t.resourcename;
		for (Enumeration<VariableNameDeclaration> e = t.table.elements(); e
				.hasMoreElements();)
		{
			VariableNameDeclaration v = e.nextElement();
			table.put(v, v);
		}
		this.hasreturned = t.hasreturned;
		this.isReleased = t.isReleased;
		this.forLoop = t.forLoop;
		
	}

	/** 拷贝 */
	@Override
	public FSMRelatedCalculation copy()
	{
		FSMRelatedCalculation r = new AliasSet(this);
		return r;
	}

	private Hashtable<VariableNameDeclaration, VariableNameDeclaration> table = new Hashtable<VariableNameDeclaration, VariableNameDeclaration>();

	public void add(VariableNameDeclaration v)
	{
		table.put(v, v);
	}

	public void remove(VariableNameDeclaration v)
	{
		table.remove(v);
	}

	public boolean isEmpty()
	{
		return table.isEmpty() && !this.hasreturned;
	}

	/** 设置标记节点 */
	public void setResource(SimpleNode resource)
	{
		setTagTreeNode(resource);
	}

	public SimpleNode getResource()
	{
		return getTagTreeNode();
	}

	public void setResouceName(String resourcename)
	{
		this.resourcename = resourcename;
	}

	public String getResourceName()
	{
		return this.resourcename;
	}

	public boolean contains(VariableNameDeclaration v)
	{
		return table.containsKey(v);
	}

	public Hashtable<VariableNameDeclaration, VariableNameDeclaration> getTable()
	{
		return table;
	}

	public void setTable(
			Hashtable<VariableNameDeclaration, VariableNameDeclaration> table)
	{
		this.table = table;
	}

	/** 计算数据流方程中的IN */
	@Override
	public void calculateIN(FSMMachineInstance fsmin, VexNode n, Object data)
	{
		if (fsmin.getRelatedObject() != this)
		{
			throw new RuntimeException("AliasSet error");
		}
		List<Edge> list = new ArrayList<Edge>();
		for (Enumeration<Edge> e = n.getInedges().elements(); e
				.hasMoreElements();)
		{
			list.add(e.nextElement());
		}
		Collections.sort(list);
		Hashtable<VariableNameDeclaration, VariableNameDeclaration> newtable = new Hashtable<VariableNameDeclaration, VariableNameDeclaration>();
		// 合并所有入边的alias set
		boolean hasreturned = false;
		for (Edge edge : list)
		{
			VexNode pre = edge.getTailNode();// 获得edge边的尾节点
			if (pre.getFSMMachineInstanceSet() != null)
			{
				FSMMachineInstance prefsmin = pre.getFSMMachineInstanceSet()
						.getTable().get(fsmin);
				if (prefsmin != null)
				{
					AliasSet s1 = (AliasSet) prefsmin.getRelatedObject();
					Hashtable<VariableNameDeclaration, VariableNameDeclaration> table1 = s1
							.getTable();
					if (!s1.isEmpty())
					{
						if (s1.hasreturned)
						{
							hasreturned = true;
						}
						else
						{
							hasreturned = false;
						}
					}
					for (Enumeration<VariableNameDeclaration> e = table1
							.elements(); e.hasMoreElements();)
					{
						VariableNameDeclaration v = e.nextElement();

						newtable.put(v, v);
					}
					// 不考虑资源分配的路径，分配失败的路进默认已经释放
					/*
					 * if (resourcename.equals("Resource")) { if
					 * (pre.getDomain(v) instanceof PointDomain &&
					 * !((PointDomain)pre.getDomain(v)).isUnknown()) {
					 * PointDomain domain = (PointDomain) pre.getDomain(v); if
					 * (domain.range.isCanonical() && domain.range.isIn(0)) {
					 * continue; } } }
					 */
				}
			}
		}
		this.hasreturned = hasreturned;
		setTable(newtable);
		/*
		 * boolean bfirst = true; Iterator<Edge> iter = list.iterator(); while
		 * (iter.hasNext()) { Edge edge = iter.next(); VexNode pre =
		 * edge.getTailNode();
		 * 
		 * if (pre.getFSMMachineInstanceSet() != null) { FSMMachineInstance
		 * prefsmin = pre.getFSMMachineInstanceSet().getTable().get(fsmin); if
		 * (prefsmin != null) { if (bfirst) { bfirst = false;
		 * Hashtable<VariableNameDeclaration, VariableNameDeclaration> table1,
		 * newtable; AliasSet s1 = (AliasSet) prefsmin.getRelatedObject();
		 * table1 = s1.getTable(); newtable = new
		 * Hashtable<VariableNameDeclaration, VariableNameDeclaration>();
		 * 
		 * for (Enumeration<VariableNameDeclaration> e = table1 .elements();
		 * e.hasMoreElements();) { VariableNameDeclaration v = e.nextElement();
		 * newtable.put(v, v); } setTable(newtable); hasreturned =
		 * s1.hasreturned; } else { Hashtable<VariableNameDeclaration,
		 * VariableNameDeclaration> table1, table2, newtable; AliasSet s1 =
		 * (AliasSet) fsmin.getRelatedObject(); AliasSet s2 = (AliasSet)
		 * prefsmin.getRelatedObject(); table1 = s1.getTable(); table2 =
		 * s2.getTable(); newtable = new Hashtable<VariableNameDeclaration,
		 * VariableNameDeclaration>(); // 求并集 for
		 * (Enumeration<VariableNameDeclaration> e = table1 .elements();
		 * e.hasMoreElements();) { VariableNameDeclaration v = e.nextElement();
		 * newtable.put(v, v); } for (Enumeration<VariableNameDeclaration> e =
		 * table2 .elements(); e.hasMoreElements();) { VariableNameDeclaration v
		 * = e.nextElement(); newtable.put(v, v); } setTable(newtable); if
		 * (s1.hasreturned && s2.hasreturned) { hasreturned = true; } } } } }
		 */
	}

	/** 计算数据流方程中的OUT */
	@Override
	public void calculateOUT(FSMMachineInstance fsmin, VexNode n, Object data)
	{
		if (fsmin.getRelatedObject() != this)
		{
			throw new RuntimeException("AliasSet error");
		}

		List evaluationResults = null;
		SimpleNode treenode = n.getTreenode();
		// 处理赋值
		// xpath不处理那些尾节点
		if (treenode != null
				&& treenode.getVexlist().get(0) == n
				&& !(treenode instanceof ASTSelectionStatement)
				&& !(treenode instanceof ASTIterationStatement)
				&& !(fsmin.getStates().getTable().size() == 1 && (fsmin
						.getStates().getTable().keys().nextElement())
						.getState().toString().equals("Start")))
		{
			
			String xPath = ".//AssignmentExpression[count(*)=3]";                        //GCC的语法和CPP不同 ，故而是3
			
			evaluationResults = StateMachineUtils.getEvaluationResults(
					treenode, xPath);
			AliasSet alias = (AliasSet) fsmin.getRelatedObject();
			if (n.getName().startsWith("exit_"))
			{
				alias.setHasReturned(true);
			}
			if (evaluationResults.size() > 0)
			{
				Iterator i = evaluationResults.iterator();
				while (i.hasNext())
				{
					SimpleNode parent = (SimpleNode)i.next();
					
					SimpleNode operator = (SimpleNode)parent.jjtGetChild(1);
					if(operator.getOperatorType().size() != 1 || !"=".equalsIgnoreCase(operator.getOperatorType().get(0)))
					{
						continue;
					}
					
					SimpleNode left = (SimpleNode)parent.jjtGetChild(0);
					SimpleNode right = (SimpleNode)parent.jjtGetChild(2);
					
					VariableNameDeclaration leftv = left.getVariableNameDeclaration();
					VariableNameDeclaration rightv = right.getVariableNameDeclaration();
					
					String xpath = ".//UnaryExpression[./UnaryOperator[@Operators='*']]/UnaryExpression/PostfixExpression/PrimaryExpression"
								+ "|.//UnaryExpression/PostfixExpression[@Operators='->']/PrimaryExpression"
								+"|.//UnaryExpression/PostfixExpression[@Operators='.']/PrimaryExpression";
								//中括号里的属性 是用的反射机制 在SimpleNode中有方法getOperators 注意大小写
					
					List<SimpleNode> re = StateMachineUtils.getEvaluationResults(parent, xpath);
					
							
					if (re != null && re.size() != 0)
					{
						ASTPrimaryExpression id = (ASTPrimaryExpression) re.get(0);
						
						if (leftv == null)
						{
							VariableNameDeclaration temp = id.getVariableDecl();
							if (temp!= null && alias.contains(temp))
							{
								// 形如: int *p = new int; *p = 1;
								continue;
							}
							else
								if (rightv != null && temp != null)
								{
									// 形如: int *p = new int; k->a = p;
									// 动态分配的指针通过参数传递到函数外部
									if (alias.contains(rightv)
											&& !alias.contains(temp)
											&& temp.isParam())
									{
										if (temp.getType() instanceof CType_Pointer)
										{
											CType_Pointer pType = (CType_Pointer) temp.getType();
											
											if (pType.getOriginaltype() instanceof CType_Pointer)
											{
												Scope scope = treenode.getScope().getEnclosingMethodScope();
												
												if (scope != null /*
																 * &&
																 * scope.getNode
																 * () instanceof
																 * ASTFunctionDefinition
																 */)
												{
													if((ASTFunctionDefinition) scope.getNode()!=null){
													MethodNameDeclaration methodDecl = ((ASTFunctionDefinition) scope.getNode()).getDecl();
													if (methodDecl != null
																&& methodDecl.getMethod() != null)
													{
														MethodMMFeature mlfFeature = new MethodMMFeature();
														mlfFeature.addMMVariable(Variable.getVariable(temp),
																					(MMFetureType) fsmin.getStateData());
														MethodSummary summary = methodDecl.getMethod().getMtSummmary();
														if (summary == null)
														{
															summary = new MethodSummary();
															methodDecl.getMethod().setMtSummmary(summary);
														}
														summary.addSideEffect(mlfFeature);
													}
												}
												}
												// **p = t, 通过参数传递指针
											}
										}
										alias.setHasReturned(true);
									}
								}
						}
					}

					if (leftv == rightv)
					{
						continue;
					}
					if (leftv == null)
					{
						// pp[0] = p; return pp
						// st->a = a; return st;
						/*xPath = ".//unary_expression/postfix_expression[@OperatorTypeString='[->]' or @OperatorTypeString='[[]]']/primary_expression/id_expression";*/
						xPath = ".//UnaryExpression[./UnaryOperator[@Operators='[]']]/UnaryExpression/PostfixExpression/PrimaryExpression"
							+ "|.//UnaryExpression/PostfixExpression[@Operators='->']/PrimaryExpression";
						
						re = StateMachineUtils.getEvaluationResults(left, xPath);
						if (re != null && re.size() != 0)
						{
							ASTPrimaryExpression id = (ASTPrimaryExpression) re.get(0);
							
							VariableNameDeclaration temp = id.getVariableDecl();
							if (alias.contains(rightv))
							{
								alias.add(temp);
							}
						}
						
						//wavericq注释掉
						/*// p = new int; this->a = p;
						xPath = ".//unary_expression/postfix_expression[./primary_expression[@Image='this']]/id_expression";
						re = StateMachineUtils
								.getEvaluationResults(left, xPath);
						if (re != null && re.size() != 0)
						{
							ASTPrimaryExpression id = (ASTPrimaryExpression) re
									.get(0);
							if (treenode.getScope().getEnclosingClassScope() != null)
							{
								alias.setHasReturned(true);
							}
						}*/
					}
					else
					{
						if (leftv instanceof VariableNameDeclaration)
						{
							if (alias.contains(leftv) && !MLFStateMachine.isNullPoint(n,true,leftv)){
								List nodes = StateMachineUtils.getEvaluationResults(treenode, ".//PrimaryExpression[@Method='true']" );
								if(nodes.size()==0)
									alias.remove(leftv);
								else if(MLFStateMachine.isValidMethod(nodes, fsmin, CheckType.C_FREE_OK) == false) 
								// 将等号左边变量从别名集合去除
								    alias.remove(leftv);
							}
							
							
							if(alias.contains(leftv))
							{
								List temp = StateMachineUtils.getEvaluationResults(right, ".//PrimaryExpression[@Method='true']" );
								if(temp.size() > 0)
								{
									Iterator it = temp.iterator();
									while(it.hasNext())
									{
										SimpleNode node = (SimpleNode)it.next();
										if(alias.getResource()!=null&&node.getImage().indexOf("malloc")!=-1 
												&& node.getBeginLine() > alias.getResource().getBeginLine())
										{
											alias.remove(leftv);
										}
									}
								}
							}
							
							
						}
						if (rightv instanceof VariableNameDeclaration && leftv instanceof VariableNameDeclaration)
						{
							if (alias.contains(rightv))
							{
								// 将等号左边变量加入别名集合
								alias.add(leftv);
							}
						}
					}
				}
			} // else
			{
				// 为了减少误报，将分配指针的地址做参数传递给其它函数则默认为是释放                       //参数传递，参数是地址/指针的地址
				/*xPath = ".//postfix_expression/expression_list//unary_expression[./unary_operator[@OperatorTypeString='[&]']]/unary_expression/postfix_expression[@OperatorTypeString='[]']/primary_expression/id_expression";
				*/
				xPath = ".//PostfixExpression/ArgumentExpressionList//UnaryExpression[./UnaryOperatpr[@Operators='&']]/UnaryExpresion/PostfixExpression/PrimaryExpression";

				List<SimpleNode> re = StateMachineUtils.getEvaluationResults(treenode, xPath);
				
				if (re != null && re.size() != 0)
				{
					ASTPrimaryExpression id = (ASTPrimaryExpression) re.get(0);
					if (id.getVariableDecl() instanceof VariableNameDeclaration)
					{
						if (alias.contains((VariableNameDeclaration) id.getVariableDecl()))
						{
							alias.setHasReturned(true);
						}
					}
				}
				
				//这里好像只能选出来++/--在前面的
				//xPath = ".//assignment_expression/pm_expression/unary_expression[(@Image='--') or (@Image='++')]/unary_expression/postfix_expression/*[last()]//descendant-or-self::id_expression";
				
				//貌似没有之前的考虑全
				xPath = ".//AssignmentExpressin/UnaryExpression[(@Operators='--') or (@Operators='++')]/UnaryExpression/PostfixExpression/PrimaryExpression";
				evaluationResults = StateMachineUtils.getEvaluationResults(treenode, xPath);
				Iterator i = evaluationResults.iterator();
				while (i.hasNext())
				{
					ASTPrimaryExpression expression = (ASTPrimaryExpression) i.next();
					
					if (expression == null
							|| !(expression.getVariableDecl() instanceof VariableNameDeclaration))
					{
						continue;
					}
					VariableNameDeclaration expressionv = (VariableNameDeclaration) expression.getVariableDecl();

					if (alias.contains(expressionv))
					{
						// 将等号左边变量从别名集合去除
						alias.remove(expressionv);
					}
				}
				
				
				
				//这个xpath级以下应该是处理++/--后置的情况 
				//xPath = ".//assignment_expression/pm_expression/unary_expression/postfix_expression/*[last()]//descendant-or-self::id_expression";
				
				xPath = ".//AssignmentExpression/UnaryExpression/PostfixExpression[(@Operators='--') or (@Operators='++')]/PrimaryExpression";
				evaluationResults = StateMachineUtils.getEvaluationResults(treenode, xPath);

				i = evaluationResults.iterator();
				while (i.hasNext() && !(treenode instanceof ASTJumpStatement))
				{
					ASTPrimaryExpression expression = (ASTPrimaryExpression) i
							.next();
					if (expression == null
							|| !(expression.getVariableDecl() instanceof VariableNameDeclaration)
					// || expression.getImages().size() < 2
					// || expression.getImages().toArray()[1].toString() != "++"
					)
					{
						continue;
					}
					VariableNameDeclaration expressionv = (VariableNameDeclaration) expression.getVariableDecl();

					if (alias.contains(expressionv))
					{
						// 将等号左边变量从别名集合去除-----？？？
						alias.remove(expressionv);
					}
				}
			}
		}
		// 处理return
		if (n.getTreenode() instanceof ASTJumpStatement
				//&& n.getTreenode().getImage().equals("return"))
				&& n.getName().startsWith("return"))
		{
			ASTJumpStatement returnstmt = (ASTJumpStatement) n.getTreenode();
			
			List conditionList = returnstmt.findChildrenOfType(ASTConditionalExpression.class);
			
			ASTConditionalExpression condition = null;
			if (!conditionList.isEmpty())
			{
				condition = (ASTConditionalExpression) conditionList.get(0);
			}
			
			// 怎么去取得VariableNameDeclaration
//			ExpressionDomainVisitor expVisitor = new ExpressionDomainVisitor();
			
			Object re = null, re1 = null;
//			VariableNameDeclaration re = null, re1 = null;
			
			if (condition == null)
			{
//				re = returnstmt.jjtAccept(expVisitor, new DomainData(false));
				List temp = returnstmt.findChildrenOfType(ASTUnaryExpression.class);
				if(temp != null && temp.size()>0)
				{
//					ASTUnaryExpression pe = (ASTUnaryExpression)temp.get(0);
//					if(pe!= null && pe.getVariableDecl() instanceof VariableNameDeclaration)
//					{
//						re = pe.getVariableDecl();
//					}
					for(int i=0;i<temp.size();i++){
						ASTUnaryExpression pe = (ASTUnaryExpression)temp.get(i);
						if(pe!= null && pe.getVariableDecl() instanceof VariableNameDeclaration)
						{
							re = pe.getVariableDecl();
							break;
						}
					}
				}
			}
			else
			{
				if (condition.jjtGetNumChildren() == 3)
				{
					/*SimpleNode conditionChild2 = (SimpleNode) condition
							.jjtGetChild(1);
					SimpleNode conditionChild3 = (SimpleNode) condition
							.jjtGetChild(2);
					re = conditionChild2.jjtAccept(expVisitor, new DomainData(
							false));
					re1 = conditionChild3.jjtAccept(expVisitor, new DomainData(
							false));*/
					
					SimpleNode conditionChild2 = (SimpleNode) condition.jjtGetChild(1);
					List temp2 = conditionChild2.findChildrenOfType(ASTPrimaryExpression.class);
					if( temp2 != null && temp2.size() >0)
					{
						ASTPrimaryExpression pe2 = (ASTPrimaryExpression)temp2.get(0);
						if(pe2 != null && pe2.getVariableDecl() instanceof VariableNameDeclaration)
						{
							re = pe2.getVariableDecl();
						}
					}
					
					SimpleNode conditionChild3 = (SimpleNode) condition.jjtGetChild(2);
					List temp3 = conditionChild3.findChildrenOfType(ASTPrimaryExpression.class);
					if( temp3 != null && temp3.size() >0)
					{
						ASTPrimaryExpression pe3 = (ASTPrimaryExpression)temp2.get(0);
						if(pe3 != null && pe3.getVariableDecl() instanceof VariableNameDeclaration)
						{
							re1 = pe3.getVariableDecl();
						}
					}
				}
			}
			
			
			
			AliasSet alias = (AliasSet) fsmin.getRelatedObject();
			Hashtable<VariableNameDeclaration, VariableNameDeclaration> table = alias.getTable();
			if (re instanceof VariableNameDeclaration)
			{				
				for(VariableNameDeclaration relatedVar :table.keySet()){
					do{
						if (relatedVar == (VariableNameDeclaration) re){
							alias.setHasReturned(true);
							break;
						}
						relatedVar = (VariableNameDeclaration) relatedVar.getFatherVariable();
					}while(relatedVar != null);
				}
			}
			if (re1 instanceof VariableNameDeclaration)
			{
				for(VariableNameDeclaration relatedVar :table.keySet()){
					do{
						if (relatedVar == (VariableNameDeclaration) re1){
							alias.setHasReturned(true);
							break;
						}
						relatedVar = (VariableNameDeclaration) relatedVar.getFatherVariable();
					}while(relatedVar != null);
				}
			}
			
			
			if (returnstmt != null)
			{
				
				//String xPath = ".//postfix_expression/primary_expression/id_expression[@Method='true']|.//declaration/declaration_specifiers/qualified_type/qualified_id[@Method='true']";
				String xPath = ".//UnaryExpression/PostfixExpression/PrimaryExpression[@Method='true']";
				List<SimpleNode> nodes = StateMachineUtils
						.getEvaluationResults(returnstmt, xPath);
				if (MLFStateMachine.checkCFreeMethod(nodes, fsmin))
				{
					alias.setHasReturned(true);
				}
			}

			//跟new表达式有关吧
			/*if (returnstmt != null)
			{
				String xPath = ".//new_expression/new_initializer/expression_list//primary_expression/id_expression | .//postfix_expression/expression_list//primary_expression/id_expression";
				List<SimpleNode> nodes = StateMachineUtils
						.getEvaluationResults(returnstmt, xPath);
				for (SimpleNode node : nodes)
				{
					ASTid_expression idExp = (ASTid_expression) node;
					if (idExp.getNameDeclaration() instanceof VariableNameDeclaration)
					{
						if (alias.contains((VariableNameDeclaration) idExp       
								.getNameDeclaration()))
						{
							alias.setHasReturned(true);
						}
					}
				}
			}*/
		}
		
		
		// 处理作用域变化
		AliasSet alias = (AliasSet) fsmin.getRelatedObject();
		// 处理作用域变化
		ArrayList<VariableNameDeclaration> todelete = new ArrayList<VariableNameDeclaration>();
		Hashtable<VariableNameDeclaration, VariableNameDeclaration> table = alias
				.getTable();
		for (Enumeration<VariableNameDeclaration> e = table.keys(); e
				.hasMoreElements();)
		{
			VariableNameDeclaration v = e.nextElement();
			Scope delscope = v.getScope();
			SimpleNode astnode = n.getTreenode();
			boolean b = true;
			if (astnode == null)
				break;// 处理for没有intial,decr等语法树的节点
			if (!astnode.getScope().isSelfOrAncestor(delscope))           //判断delscope是否是astnode的父亲/祖先
			{
				// 声明作用域已经不是当前作用域自己或父亲了
				b = true;
			}
			else if (delscope.isSelfOrAncestor(astnode.getScope())
						&& /*delscope != astnode.getScope() && */n.isBackNode())
			{
					// 当前作用域是声明作用域自己或者父亲，但是当前节点需要终止当前作用域
				b = true;
			}
			else if (astnode instanceof ASTJumpStatement
							&& delscope.isSelfOrAncestor(astnode.getScope()
									.getEnclosingMethodScope())
							&& !(delscope instanceof ClassScope))
		   {
						Hashtable<String, Edge> outedges = n.getOutedges();
						for (Edge edge : outedges.values())
						{
							if (edge.getHeadNode().getName().startsWith(
									"func_out"))                       //if 然后return是在这里做的处理
							{
								b = true;
								break;
							}
							else
								b = false;
						}
					}else if(fsmin.getRelatedASTNode().getScope().getParent().isSelfOrAncestor(astnode.getScope()) 
							&& forLoop == true && (n.getName().startsWith("for_out")||n.getName().startsWith("while_out") ||n.getName().startsWith("doWhile_finalOut") )){
						b = true;
					}
					else
					{
						b = false;
					}
			if (b)
			{
				todelete.add(v);
			}
		}

		for (VariableNameDeclaration v : todelete)
		{
			alias.remove(v);
		}
	}
}