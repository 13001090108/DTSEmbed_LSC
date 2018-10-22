package softtest.summary.gcc.fault;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import softtest.ast.c.ASTArgumentExpressionList;
import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTCompoundStatement;
import softtest.ast.c.ASTDirectDeclarator;
import softtest.ast.c.ASTFunctionDefinition;
import softtest.ast.c.ASTJumpStatement;
import softtest.ast.c.ASTParameterList;
import softtest.ast.c.ASTPostfixExpression;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTSelectionStatement;
import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.CParserVisitorAdapter;
import softtest.ast.c.Node;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.VexNode;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.PointerDomain;
import softtest.interpro.c.InterContext;
import softtest.summary.c.MethodFeatureVisitor;
import softtest.summary.c.MethodSummary;
import softtest.symboltable.c.AbstractNameDeclaration;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.Type.CType;
import softtest.symboltable.c.Type.CType_AllocType;
import softtest.symboltable.c.Type.CType_Pointer;
import softtest.symboltable.c.Type.CType_Typedef;

public class MethodMMFeatureVisitor0 extends CParserVisitorAdapter implements MethodFeatureVisitor
{
	private static MethodMMFeatureVisitor0 instance;
	
	public static MethodMMFeatureVisitor0 getInstance()
	{
		if (instance == null)
		{
			instance = new MethodMMFeatureVisitor0();
		}
		return instance;
	}
	
	private MethodMMFeatureVisitor0(){}

	public void visit(VexNode vexNode)
	{
		SimpleNode treeNode = vexNode.getTreenode();
		if(treeNode == null || !(treeNode instanceof ASTFunctionDefinition))
		{
			return;
		}
		
		//增加了对函数返回类型的判断
		boolean returnPointer = false;
		ASTFunctionDefinition func = (ASTFunctionDefinition)treeNode;
		MethodNameDeclaration decl = func.getDecl();
		CType returnType = decl.getMethod().getReturnType();
		if(returnType instanceof CType_Typedef)
		{
			CType_Typedef typedef = (CType_Typedef)returnType;
			returnType = typedef.getOriginaltype();
		}
		if(returnType instanceof CType_Pointer)
		{
			returnPointer = true;
		}
		
		VisitData data = new VisitData();
		
		SimpleNode parameterList = (SimpleNode)treeNode.getFirstChildOfType(ASTParameterList.class);
		if(parameterList != null)
		{
			parameterList.jjtAccept(this, data);
		}
		List<AbstractNameDeclaration> parameters = data.vlist;
		
		if(parameters.size() == 0)
		{
			return; //???          这个好像没有道理啊
		}
		
		int paramIndex = -1;
		for(int i=0; i<parameters.size(); i++)
		{
			if(parameters.get(i) instanceof VariableNameDeclaration)
			{
				VariableNameDeclaration parameter = (VariableNameDeclaration)parameters.get(i);
				if(parameter.getType() instanceof CType_Pointer)
				{
					data.alias.add(parameter);
					paramIndex = i+1;
					break;                                                                                  //目前只考虑有一个指针参数的情况
				}
			}
		}
		
		data.vlist.clear();
		SimpleNode compoundStatement = (SimpleNode)treeNode.getFirstChildOfType(ASTCompoundStatement.class);
		if(compoundStatement != null)
		{
			compoundStatement.jjtAccept(this, data);
		}
		
		
		
		MethodMMFeature0 mlfFeature = new MethodMMFeature0();
		mlfFeature.setMMRelease(data.isAllocFree);
		if(returnPointer)
		{
			mlfFeature.setMMAllocate(data.isReturnAlloc);
		}
		mlfFeature.setParamIndex(paramIndex);
		
		MethodSummary summary = InterContext.getMethodSummary(vexNode);
		if(summary != null)
		{
			summary.addSideEffect(mlfFeature);
		}
	}
	
	public Object visit(ASTJumpStatement node, Object data)
	{
		if( !(data instanceof VisitData))
		{
			return null;
		}
		
		VisitData visitData = (VisitData)data;
		
		VexNode vex = node.getCurrentVexNode();                         //注是用currentVexNode()方法
		if(vex.getContradict())
		{
			return null;
		}
		
		if("return".equals(node.getImage()))
		{
			if(node.jjtGetNumChildren() > 0)
			{
				int sn = visitData.vlist.size();
				SimpleNode cnode = (SimpleNode)node.jjtGetChild(0);
				cnode.jjtAccept(this, visitData);
				int en = visitData.vlist.size() - sn;
				for(int i=0; i<en; i++)
				{
					AbstractNameDeclaration decl = visitData.vlist.get(i);
					if(decl instanceof VariableNameDeclaration)
					{
						VariableNameDeclaration varDecl = (VariableNameDeclaration)decl;
						
						vex.setfsmCompute(false);
						Domain varDomain = vex.getDomain(varDecl);
						
						if(varDomain instanceof PointerDomain)
						{
							PointerDomain pVarDomain = (PointerDomain)varDomain;
							if(pVarDomain.Type.contains(CType_AllocType.heapType))
							{
								visitData.isReturnAlloc = true;
								break;
							}
						}
					}
					if(decl instanceof MethodNameDeclaration)
					{
						MethodNameDeclaration methodDecl = (MethodNameDeclaration)decl;
						
						if(methodDecl.getMethodSummary() != null)
						{
							MethodMMFeature0 mlfFeature = (MethodMMFeature0)methodDecl.getMethodSummary().findMethodFeature(MethodMMFeature0.class);
							if(mlfFeature != null && mlfFeature.isMMAllocate())
							{
								visitData.isReturnAlloc = true;
								break;
							}
						}
						
						
						/*boolean flag = false;
						if("malloc".equals(methodDecl.getImage()) 
								|| "calloc".equals(methodDecl.getImage())
								|| "realloc".equals(methodDecl.getImage())
								|| "strup".equals(methodDecl.getImage()))
						{
							flag = true;
						}
						else
						{
							if(methodDecl.getMethodSummary() != null)
							{
								MethodMMFeature0 mlfFeature = (MethodMMFeature0)methodDecl.getMethodSummary().findMethodFeature(MethodMMFeature0.class);
								if(mlfFeature != null && mlfFeature.isMMAllocate())
								{
									flag = true;
								}
							}
						}
						
						if(flag)
						{
							visitData.isReturnAlloc = true;
							break;
						}*/
					}
				}
			}
			
		}
		else
		{
			super.visit(node, visitData);
		}
		
		return null;
	}
	
	/**没有考虑不可达路径的问题 整个这个类里的方法都没有考虑不可达路径的问题
	 * 现在加上了
	 * ！！！问题是这个合并对不对
	 * */
	
	public Object visit(ASTSelectionStatement node, Object data)
	{
		if( !(data instanceof VisitData))
		{
			return null;
		}
		
		VisitData visitData = (VisitData)data;
		
		VexNode vex = node.getCurrentVexNode();                         //注是用currentVexNode()方法
		if(vex.getContradict())
		{
			return null;
		}
		
		if("if".equals(node.getImage()))
		{
			int sn = visitData.vlist.size();
			Node expression = node.jjtGetChild(0);
			expression.jjtAccept(this, visitData);
			int en = visitData.vlist.size() - sn;
			boolean flag = true;                                          //true表示if的条件只与alias中的变量有关, alias中的变量语义上都指向同一个内存空间
			for(int i=0; i<en; i++)                                   //en必须得等于1么
			{
				AbstractNameDeclaration decl = visitData.vlist.get(i);
				if(!(decl instanceof VariableNameDeclaration) || !visitData.alias.contains(decl))
				{
					flag = false;
					break;
				}
			}
			
			Set<VariableNameDeclaration> origin = new HashSet<VariableNameDeclaration>(visitData.alias);
			if(node.jjtGetNumChildren() == 2)                                                                 //这样合并没有考虑不可达路径的问题
			{
				Node cnode = node.jjtGetChild(1);
				cnode.jjtAccept(this, visitData);
				if(!flag || !visitData.isAllocFree)
				{
					visitData.alias.addAll(origin);
					visitData.isAllocFree = false;
				}
				
			}
			if(node.jjtGetNumChildren() == 3)
			{
				Node c1node = node.jjtGetChild(1);
				c1node.jjtAccept(this, visitData);
				Set<VariableNameDeclaration> tempAlias = visitData.alias;
				boolean tempFree = visitData.isAllocFree;
				visitData.alias = origin;
				
				Node c2node = node.jjtGetChild(2);
				c2node.jjtAccept(this, visitData);
				
				if(!(flag && (tempFree || visitData.isAllocFree)))
				{
					visitData.alias.addAll(tempAlias);
					visitData.isAllocFree = false;
				}
			}
		}
		else
		{
			super.visit(node, visitData);
		}
		
		
		return null;
	}
	
	public Object visit(ASTAssignmentExpression node, Object data)
	{
		if( !(data instanceof VisitData))
		{
			return null;
		}
		
		VisitData visitData = (VisitData)data;
		
		VexNode vex = node.getCurrentVexNode();                         //注是用currentVexNode()方法
		if(vex.getContradict())
		{
			return null;
		}
		
		if(node.jjtGetNumChildren() == 3)
		{
			SimpleNode operator = (SimpleNode)node.jjtGetChild(1);
			if("=".equals(operator.getOperators()))                     //if(operator.getOperatorType().size() == 1 && "=".equalsIgnoreCase(operator.getOperatorType().get(0)))
			{
				SimpleNode left = (SimpleNode)node.jjtGetChild(0);
				SimpleNode right = (SimpleNode)node.jjtGetChild(2);
				
				/**先右后左的顺寻，也符合=的右结合性*/
				right.jjtAccept(this, visitData);
				
				//怎么会有越界的异常呢 java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
				if(visitData.vlist.size() == 0)
				{
					return null;
				}
				
				
				AbstractNameDeclaration rv = visitData.vlist.get(0);                                 //如果先左后右应该是拿的是式子a=b...=c最右边的这样不利于处理+=表达式
				
				left.jjtAccept(this, visitData);
				
				/*if(! (visitData.vlist.get(0) instanceof VariableNameDeclaration))
				{
					System.err.println("出错了 MethodMMFeatureVisitor0 ：： visit(ASTAssignmentExpression node");
					System.err.println(node.getFileName());
					System.err.println(node.getBeginLine());
					System.err.println(vex.getName());
					System.err.println(visitData.vlist.get(0));
				}*/
				
				/**这里会报错误  怎么回事*/
//				VariableNameDeclaration lv = (VariableNameDeclaration)visitData.vlist.get(0);
				if(!(visitData.vlist.get(0) instanceof VariableNameDeclaration))
				{
					return null;
				}
				VariableNameDeclaration lv = (VariableNameDeclaration)visitData.vlist.get(0);
				
				/**这里是否需要加一个判断：lv!=null 和 lv不等于遍历left之前vlist.get(0)
				 * 应该不用 =赋值表达是左边必然有一个变量 要不然编译都不能同过
				 * */
				if(rv instanceof VariableNameDeclaration)                                        //instanceof应该能防null吧
				{
					if(visitData.alias.contains(rv))
					{
						visitData.alias.add(lv);
					}
					else
					{
						visitData.alias.remove(lv);
					}
				}
				else
					if(rv instanceof MethodNameDeclaration)
					{
						visitData.alias.remove(lv);
					}
				
			}
			else
			{
				super.visit(node, data);
			}
		}
		else
		{
			super.visit(node, data);
		}
		
		return null;
	}
	
	public Object visit(ASTUnaryExpression node, Object data)
	{
		if( !(data instanceof VisitData))
		{
			return null;
		}
		
		VisitData visitData = (VisitData)data;
		
		VexNode vex = node.getCurrentVexNode();                         //注是用currentVexNode()方法
		if(vex.getContradict())
		{
			return null;
		}
		
		super.visit(node, visitData);
		
		if("++".equals(node.getOperators()) || "--".equals(node.getOperators()))
		{
			VariableNameDeclaration v = (VariableNameDeclaration)visitData.vlist.get(0);
			visitData.alias.remove(v);
		}
		
		return null;
	}
	
	public Object visit(ASTPostfixExpression node, Object data)
	{
		if( !(data instanceof VisitData))
		{
			return null;
		}
		
		VisitData visitData = (VisitData)data;
		
		VexNode vex = node.getCurrentVexNode();                         //注是用currentVexNode()方法
		if(vex.getContradict())
		{
			return null;
		}
		
		super.visit(node, visitData);
		
		if("++".equals(node.getOperators()) || "--".equals(node.getOperators()))
		{
			VariableNameDeclaration v = (VariableNameDeclaration)visitData.vlist.get(0);                  //只能增加一个吧 且肯定是VariableNameDeclaration
			visitData.alias.remove(v);
		}
		
		return null;
	}
	
	public Object visit(ASTPrimaryExpression node, Object data)
	{
		if( !(data instanceof VisitData))
		{
			return null;
		}
		
		VisitData visitData = (VisitData)data;
		
		VexNode vex = node.getCurrentVexNode();                         //注是用currentVexNode()方法
		if(vex.getContradict())
		{
			return null;
		}
		
		super.visit(node, data);                       //放在这里合适么
		
		
		
		if(node.isMethod() && node.getMethodDecl() != null)
		{
			MethodNameDeclaration methodDecl = node.getMethodDecl();
			if(methodDecl.getMethodSummary() != null)
			{
				MethodMMFeature0 mlfFeature = (MethodMMFeature0)methodDecl.getMethodSummary().findMethodFeature(MethodMMFeature0.class);
				if(mlfFeature != null && mlfFeature.isMMRelease())
				{
					int paramIndex = mlfFeature.getParamIndex();
					SimpleNode argumentList = (SimpleNode)node.getNextSibling();
					
					/*if(paramIndex < 0)
					{
						System.err.println("ERROR! ParamIndex :: " + paramIndex);
					}*/
					
					
					if(argumentList != null && argumentList.jjtGetNumChildren() >= paramIndex && paramIndex > 0)
					{
						
						SimpleNode argument = (SimpleNode)argumentList.jjtGetChild(paramIndex-1);
						VisitData vd = new VisitData();
						super.visit((SimpleNode)argument, vd);
						for(int i=0; i<vd.vlist.size(); i++)
						{
							if(vd.vlist.get(i) instanceof VariableNameDeclaration)
							{
								VariableNameDeclaration v = (VariableNameDeclaration)vd.vlist.get(i);
								if(visitData.alias.contains(v))
								{
									visitData.isAllocFree = true;
//									visitData.alias.clear();                          //???为什么注释掉清空呢
									break;
								}
								
							}
						}
					}
				}
			}
			
		}
		
		
		
		
		/*if(node.isMethod() && node.getMethodDecl() != null)
		{
			MethodNameDeclaration methodDecl = node.getMethodDecl();
			
			*//**方法相关操作*//*
			boolean flag = false;
			if(methodDecl != null && "free".equals(methodDecl.getImage()))
			{
				flag = true;
			}
			else
			{
				if(methodDecl.getMethodSummary() != null)
				{
					MethodMMFeature0 mlfFeature = (MethodMMFeature0)methodDecl.getMethodSummary().findMethodFeature(MethodMMFeature0.class);
					if(mlfFeature != null && mlfFeature.isMMRelease())
					{
						flag = true;
					}
				}
			}
			
			if(flag)
			{
				SimpleNode argumentList = (SimpleNode)node.getNextSibling();
				if(argumentList != null)
				{
					VisitData vd = new VisitData();
					super.visit((SimpleNode)argumentList, vd);
					for(int i=0; i<vd.vlist.size(); i++)
					{
						if(vd.vlist.get(i) instanceof VariableNameDeclaration)
						{
							VariableNameDeclaration v = (VariableNameDeclaration)vd.vlist.get(i);
							if(visitData.alias.contains(v))
							{
								visitData.isAllocFree = true;
//								visitData.alias.clear();
								break;
							}
							
						}
					}
				}
			}
			
			visitData.vlist.add(0, methodDecl);                          //？？？这个是为了赋值表达式的判断
		}*/
		
		
		
		
		else
		{
			VariableNameDeclaration v = node.getVariableDecl();
			if(v != null)
			{
				visitData.vlist.add(0, v);
			}
		}
		
		return null;
	}
	
	public Object visit(ASTDirectDeclarator node, Object data)
	{
		if( !(data instanceof VisitData))
		{
			return null;
		}
		
		VisitData visitData = (VisitData)data;
		
		VexNode vex = node.getCurrentVexNode();                         //注是用currentVexNode()方法
		if(vex.getContradict())
		{
			return null;
		}
		
		super.visit(node, data);                       //放在这里合适么
		
		if(node.getDecl() != null && node.getDecl() instanceof AbstractNameDeclaration)
		{
			AbstractNameDeclaration decl = (AbstractNameDeclaration)node.getDecl();
			visitData.vlist.add(decl);
		}
		
		return null;
	}
	
	public Object visit(ASTArgumentExpressionList node, Object data)                     //！！！屏蔽遍历ASTArgumentExpressionList节点
	{
		return null;
	}
	
	public Object Visit(SimpleNode node, Object data)
	{
	
		VexNode vex = node.getCurrentVexNode();                         //注是用currentVexNode()方法
		if(vex.getContradict())
		{
			return null;
		}
		
		node.childrenAccept(this, data);
		
		return null;
	}
	
	
	
	class VisitData
	{
		boolean isReturnAlloc = false;
		
		boolean isAllocFree = false;
		
		Set<VariableNameDeclaration> alias = new HashSet<VariableNameDeclaration>();
		
		List<AbstractNameDeclaration> vlist = new LinkedList<AbstractNameDeclaration>();                //这个结构适宜add(0,...)操作么
		//其实vlist可以替换为VariableNameDeclaration var一样能够满足ASTAssignmentExpression处理的要求 但是考虑到return p? p: malloc 还有if(p&q)取出这些表达式中primary中的Declaration
	}
	
	
}
