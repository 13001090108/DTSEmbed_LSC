package softtest.rules.keilc.fault;

import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTConstant;
import softtest.ast.c.ASTDeclarator;
import softtest.ast.c.ASTFunctionDefinition;
import softtest.ast.c.ASTInitDeclarator;
import softtest.ast.c.ASTPostfixExpression;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTRelationalExpression;
import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.AbstractExpression;
import softtest.ast.c.SimpleNode;
import softtest.domain.c.analysis.ExpressionValueVisitor;
import softtest.domain.c.analysis.ExpressionVistorData;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.IntegerDomain;
import softtest.domain.c.interval.IntegerInterval;
import softtest.domain.c.symbolic.Expression;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.Type.CType;
import softtest.symboltable.c.Type.CType_BaseType;

/**
 * Datatype OverFlow
 * 检测数据类型在赋值时有没有溢出，目前只检查如下类型：(unsigned)int/char/short
 * 
 * <p>目前的遗留问题：本模式既需要检测全局变量初始化时赋值是否越界，也需要检测文件内部变量赋值及比较表达式是否
 * 越界，所以本自动机既是全局作用域（Scope="File")，又要求是路径敏感的（消除不可达路径的误报）;而实际上
 * 无法实现这种模式。。。目前本自动机设置为非路径敏感！
 * 2010.4.23
 * </p>
 * @author zys	
 * 2010-4-13
 */
public class DOFStateMachine {
	
	public static List<FSMMachineInstance> createDOFStateMachines(SimpleNode node, FSMMachine fsm) 
	{
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();   
		 //查找当前源文件中所有的赋值操作,包括声明时初始化赋值(InitDeclarator)与表达式赋值(AssignmentExpression)
		String xpath = ".//InitDeclarator[count(*)=2] | " +
					   ".//AssignmentExpression[count(*)=3] | " +
					   ".//AssignmentExpression[/UnaryExpression/PostfixExpression[@Operators='++']] | "+
					   ".//AssignmentExpression[/UnaryExpression/PostfixExpression[@Operators='--']] | "+
					   ".//AssignmentExpression[/UnaryExpression[@Operators='++']/UnaryExpression/PostfixExpression] | "+
					   ".//AssignmentExpression[/UnaryExpression[@Operators='--']/UnaryExpression/PostfixExpression] |" +
					   ".//RelationalExpression|"+
					   //".//AssignmentExpression[not(./UnaryExpression)]"; 
					   ".//AssignmentExpression/UnaryExpression/PostfixExpression[@Operators='(']//AssignmentExpression[not(./UnaryExpression)]";
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		
		for(SimpleNode tempNode : evaluationResults)
		{
			if(tempNode instanceof ASTInitDeclarator)
			{
				ASTDeclarator declarator=(ASTDeclarator) tempNode.jjtGetChild(0);
				CType type=declarator.getType();
				
				//如果是函数外对变量初始化时赋值：编译器会报warning
				if(tempNode.getParentsOfType(ASTFunctionDefinition.class).size()==0)
				{
					VariableNameDeclaration v=declarator.getVariableNameDeclaration();
					if(v!=null && v.getVariable()!=null)
					{
						Object value=v.getVariable().getValue();
						if(value.getClass() == Long.class)
						{
							try{
								long t=((Long)value).longValue();
								IntegerDomain valueDomain=new IntegerDomain(t,t);
								if(compareDomain(type, valueDomain))
								{
									addFSM(list, declarator, fsm, valueDomain,null);
									continue;
								}
							}catch(NumberFormatException e){
								//如果parseLong(value)数据过大，则发生转换异常，此时直接上报IP
								//e.printStackTrace();
								addFSM(list, declarator, fsm, IntegerDomain.getFullDomain(),null);
								continue;
							}
						}
					}
				}else
				{
					//如果是函数内部初始化时赋值，则通过区间计算初始化表达式＝号右侧的值
						IntegerDomain valueDomain=domainBuilder(declarator);
						if(valueDomain==null || valueDomain.equals(new IntegerDomain(new IntegerInterval())))
							continue;
						if (compareDomain(declarator.getType(), valueDomain)) {
							addFSM(list, declarator, fsm, valueDomain,null);
							continue;
						}
				}
			} else if (tempNode instanceof ASTAssignmentExpression){
				ASTPrimaryExpression p = (ASTPrimaryExpression) ((SimpleNode) tempNode.jjtGetChild(0)).getSingleChildofType(ASTPrimaryExpression.class);
				//chh  除表达式的其他AssignmentExpression
				if(tempNode.jjtGetNumChildren()==3||
							(tempNode.jjtGetNumChildren()==1&&tempNode.jjtGetChild(0) instanceof ASTUnaryExpression&&
									p!=null&&!p.isMethod())){
					if (p != null) {
						IntegerDomain valueDomain=domainBuilder(p);
						if(valueDomain==null || valueDomain.equals(new IntegerDomain(new IntegerInterval())))
							continue;
						if (compareDomain(p.getType(), valueDomain)) {
							addFSM(list, p, fsm, valueDomain,null);
							continue;
						}
					}
				}
				//chh  表达式AssignmentExpression[not(./UnaryExpression)]
				else
				{
						ExpressionValueVisitor expvst = new ExpressionValueVisitor();
						ExpressionVistorData visitdata = new ExpressionVistorData();
						if(tempNode.getCurrentVexNode()== null)continue;
						else  visitdata.currentvex = tempNode.getCurrentVexNode();

						visitdata.currentvex.setfsmCompute(true);
						expvst.visit( tempNode, visitdata);
						visitdata.currentvex.setfsmCompute(false);
						
						Expression value1 = visitdata.value;
						
						IntegerDomain valueDomain ;
						if(value1!=null&&visitdata.currentvex.getLastsymboldomainset()!=null)
							valueDomain= (IntegerDomain)value1.getDomain(visitdata.currentvex.getLastsymboldomainset());
						else continue;
						if(valueDomain==null || valueDomain.equals(new IntegerDomain(new IntegerInterval())))
							continue;
						if (compareDomain(((AbstractExpression)(tempNode.jjtGetChild(0))).getType(), valueDomain)) {
							addFSM(list, (SimpleNode)tempNode.jjtGetChild(0), fsm, valueDomain,null);
							continue;
						}
				}
			}else if (tempNode instanceof ASTRelationalExpression)
			{
				//目前暂时不处理复杂的比较表达式，如i+j<5	i<j+k	i<j*3
				SimpleNode left=(SimpleNode) tempNode.jjtGetChild(0);
				SimpleNode right=(SimpleNode) tempNode.jjtGetChild(1);
				IntegerDomain leftDomain=null;
				IntegerDomain rightDomain=null;
				ASTPrimaryExpression leftPri=(ASTPrimaryExpression) left.getSingleChildofType(ASTPrimaryExpression.class);
				if(leftPri!=null)
				{
					leftDomain=domainBuilder(leftPri);
				}
				ASTPrimaryExpression rightPri=(ASTPrimaryExpression) right.getSingleChildofType(ASTPrimaryExpression.class);
				if(rightPri!=null)
				{
					rightDomain=domainBuilder(rightPri);
				}
				
				//取左、右表达式任意一方的类型信息（目前假定左右类型相同）
				CType type=null;
				if(leftPri!=null)
					type=leftPri.getType();
				//判断左右区间是否冲突
				if(rightDomain!=null && type!=null)
				{
					if (compareDomain(type, rightDomain)) {
						addFSM(list, tempNode, fsm, leftDomain,rightDomain);
						continue;
					}
				}
			}
		}
		return list;
	}
	
	/**
	 * @param list
	 * @param node
	 * @param fsm
	 * @param domain1
	 * @param domain2
	 * 如果是赋值表达式中生成自动机，则domain2为null,生成的desp描述中为变量信息
	 * 如果是比较表达式中生成自动机，则domain2代表表达式右侧区间，desp相应地进行描述
	 */
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm,Domain domain1,Domain domain2) {
		//System.out.println("当前创建第"+(num++)+"个自动机！");
		FSMMachineInstance fsminstance = fsm.creatInstance();
		VariableNameDeclaration v=node.getVariableNameDeclaration();
		String varName="";
		CType type=null;
		if(v!=null)
		{
			varName=v.getImage();
			type=v.getType();
		}
		fsminstance.setRelatedASTNode(node);
		fsminstance.setReleatedVexNode(node.getCurrentVexNode());
		if(domain2==null)
		{
			fsminstance.setDesp("位于第"+node.getBeginLine()+"行的变量" + varName + ",数据类型为"+type
				+",赋值区间为"+domain1+"，导致数据类型溢出");
		}
		else
		{
			ASTUnaryExpression left=(ASTUnaryExpression) node.jjtGetChild(0);
			ASTUnaryExpression right=(ASTUnaryExpression) node.jjtGetChild(1);
			ASTPrimaryExpression leftPri=(ASTPrimaryExpression) left.getSingleChildofType(ASTPrimaryExpression.class);
			ASTPrimaryExpression rightPri=(ASTPrimaryExpression) right.getSingleChildofType(ASTPrimaryExpression.class);

			fsminstance.setDesp("位于第"+node.getBeginLine()+"行的比较表达式：左侧变量" + leftPri.getImage() + "(区间为："+domain1+")与右侧变量"+rightPri.getImage()
					+"区间为("+domain2+")，二者比较时导致数据类型溢出");
		}
		
			list.add(fsminstance);
		
	}
	
	private static IntegerDomain domainBuilder(SimpleNode node)
	{
		VariableNameDeclaration var=null;
		Expression value=null;
		IntegerDomain domain=null;
		if(node instanceof ASTDeclarator)
		{
			var = ((ASTDeclarator)node).getVariableNameDeclaration();
			if(var==null)
				return null;
			value=node.getCurrentVexNode().getValue(var);
			((ASTDeclarator)node).setType(var.getType());
		}else if(node instanceof ASTPrimaryExpression)
		{
			var= ((ASTPrimaryExpression) node).getVariableDecl();
			if(var!=null)
			{
				value = node.getCurrentVexNode().getValue(var);
				((ASTPrimaryExpression)node).setType(var.getType());
			}else
			{
				//如果可以找到常量赋值表达式
				ASTConstant cons=(ASTConstant) node.getSingleChildofType(ASTConstant.class);
				if(cons!=null)
				{
					long t=cons.getValue();
					domain=new IntegerDomain(t,t);
					return domain;
				}else
				{
					//如果是比较复杂的表达式，比如if((i-j)<5)，直接返回空域
					return null;
				}
			}
		}
		
		if(value==null)
		{
			domain=Domain.castToIntegerDomain(node.getCurrentVexNode().getVarDomainSet().getDomain(var));
		}else{
			domain = Domain.castToIntegerDomain(
										value.getDomain(node.getCurrentVexNode().getSymDomainset()));
		}
		
		return domain;
	}
	
	private static boolean compareDomain(CType type,IntegerDomain valueDomain)
	{
		if(type.getName().equals(CType_BaseType.charType.toString()))
		{
			IntegerDomain fullDomain=IntegerDomain.getFullDomain(CType_BaseType.charType);
			if(fullDomain.getMax()<valueDomain.getMin() || fullDomain.getMin()>valueDomain.getMax())
			{
				return true;
			}
		}else if(type.getName().equals(CType_BaseType.uCharType.toString()))
		{
			IntegerDomain fullDomain=IntegerDomain.getFullDomain(CType_BaseType.uCharType);
			if(fullDomain.getMax()<valueDomain.getMin() || fullDomain.getMin()>valueDomain.getMax())
			{
				return true;
			}
		}else if(type.getName().equals(CType_BaseType.shortType.toString()))
		{
			IntegerDomain fullDomain=IntegerDomain.getFullDomain(CType_BaseType.shortType);
			if(fullDomain.getMax()<valueDomain.getMin() || fullDomain.getMin()>valueDomain.getMax())
			{
				return true;
			}
		}else if(type.getName().equals(CType_BaseType.uShortType.toString()))
		{
			IntegerDomain fullDomain=IntegerDomain.getFullDomain(CType_BaseType.uShortType);
			if(fullDomain.getMax()<valueDomain.getMin() || fullDomain.getMin()>valueDomain.getMax())
			{
				return true;
			}
		}else if(type.getName().equals(CType_BaseType.intType.toString()))
		{
			IntegerDomain fullDomain=IntegerDomain.getFullDomain(CType_BaseType.intType);
			if(fullDomain.getMax()<valueDomain.getMin() || fullDomain.getMin()>valueDomain.getMax())
			{
				return true;
			}
		}else if(type.getName().equals(CType_BaseType.uIntType.toString()))
		{
			IntegerDomain fullDomain=IntegerDomain.getFullDomain(CType_BaseType.uIntType);
			if(fullDomain.getMax()<valueDomain.getMin() || fullDomain.getMin()>valueDomain.getMax())
			{
				return true;
			}
		}else if(type.getName().equals(CType_BaseType.sfrType.toString()))
		{
			IntegerDomain fullDomain=IntegerDomain.getFullDomain(CType_BaseType.sfrType);
			if(fullDomain.getMax()<valueDomain.getMin() || fullDomain.getMin()>valueDomain.getMax())
			{
				return true;
			}
		}else if(type.getName().equals(CType_BaseType.sfr16Type.toString()))
		{
			IntegerDomain fullDomain=IntegerDomain.getFullDomain(CType_BaseType.sfr16Type);
			if(fullDomain.getMax()<valueDomain.getMin() || fullDomain.getMin()>valueDomain.getMax())
			{
				return true;
			}
		}else if(type.getName().equals("pointer"))
		{
			//暂不处理指针类型
		}
		
		return false;
	}
}
