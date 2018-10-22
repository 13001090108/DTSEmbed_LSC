package softtest.rules.gcc.rule;

import java.util.LinkedList;
import java.util.List;


import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.*;
import softtest.symboltable.c.Type.*;


/** 
 * @author zhouhb
 * Signed Variable Shift Operator
 * 禁止对有符号类型进行移位运算(char类型暂当有符号数，书上说根据编译器而定)
 * (运算处理类)
 */
public class SVSOStateMachine {
	
	//移位操作只有两子节点，同时右操作数为constant.
	//add by zhouhb
	//2010.3.1
	////移位操为赋值运算<<=或者>>=
	private static String xpath = ".//ShiftExpression[count(child::UnaryExpression)>1 and ./UnaryExpression[2]/PostfixExpression/PrimaryExpression/Constant]/UnaryExpression[1]|"+
	                              ".//AssignmentExpression[/AssignmentOperator[@Operators='<<=']";
	//移位的左操作数是个&运算(单独处理，unsigned int & 0X3E -> unsigned int)表达式计算时统一把其当成int
	private static String xpath1 = "./UnaryExpression/PostfixExpression/PrimaryExpression/Expression/AssignmentExpression/ANDExpression[count(child::UnaryExpression)=2]";
    
	private static List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
	private static List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
	
	public static List<FSMMachineInstance> createSVSOMachines(SimpleNode node, FSMMachine fsm){
		AbstractExpression result = null;
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		/*
		 * 版本2：考虑所有的表达式类型，但是对按位与运算的表达式单独处理（表达式类型计算时统一把&操作当成int型）
		 * modified by zx 09.09.18
		 */
		for (SimpleNode snode : evaluationResults) {
			AbstractExpression exp = (AbstractExpression)snode;
			//左值为有符号类型
			if(isSigned(exp)) {
				if(!(exp instanceof ASTAssignmentExpression)){
					if(exp.getParentsOfType(ASTANDExpression.class)==null){
						List<SimpleNode> noConstants = StateMachineUtils.getEvaluationResults(snode, ".//Constant");
						if(noConstants!=null&& noConstants.size()!=0) { //移位操作符左边仅仅是个常数
							continue;
						}
					}
				}
				
				if(exp instanceof ASTUnaryExpression){
					if(exp.getParentsOfType(ASTANDExpression.class)==null){
						ASTShiftExpression shift = (ASTShiftExpression) exp.getFirstParentOfType(ASTShiftExpression.class);
						if(shift!=null&&(shift.getOperators().equals("<<")||shift.getOperators().equals(">>"))){
							addFSMDescription(snode,fsm);
						}
					}else{
						if(exp.jjtGetParent().jjtGetParent() instanceof ASTANDExpression)
							addFSMDescription(snode,fsm);
						}
					//对于与运算&单独处理
					List<SimpleNode> ands = StateMachineUtils.getEvaluationResults(snode, xpath1);
					if(ands==null || ands.size()==0) {
						//addFSMDescription(snode,fsm);
					}else if(ands.size()==1) { //移位的左操作数是个&运算(单独处理)
						result =(AbstractExpression) ands.get(0);//左操作数是个按位与操作的表达式，因为表达式类型计算不准备，单独处理
						if(result instanceof ASTANDExpression) {
							ASTUnaryExpression left = (ASTUnaryExpression) result.jjtGetChild(0);
							ASTUnaryExpression right = (ASTUnaryExpression) result.jjtGetChild(1);
							if(isSigned(left) && isConstant(right))
								addFSMDescription(snode,fsm);
							else if(isSigned(right) && isConstant(left))
								addFSMDescription(snode,fsm);
						}
					}	
				
				}//add by zhouhb
				//2010.3.1
				//处理移位赋值
				else if(exp instanceof ASTAssignmentExpression&&exp.jjtGetNumChildren()==3){
					ASTAssignmentOperator opt=(ASTAssignmentOperator)exp.jjtGetChild(1);
					if(opt.getOperators().equals("<<=")||opt.getOperators().equals(">>="))
						addFSMDescription(snode,fsm);
				}
			}	
		}
		
		/*
		 * 版本1： 仅仅是考虑两种情况
		 * 单变量 和 按位与操作的表达式
		 */	
//		for (SimpleNode snode : evaluationResults) {
//			List<SimpleNode> exps = StateMachineUtils.getEvaluationResults(snode, xpath1);
//			List<SimpleNode> ands = StateMachineUtils.getEvaluationResults(snode, xpath2);
//			
//			if(exps!=null && exps.size()==1) {
//				result =(AbstractExpression) exps.get(0); 
//			}else if(ands!=null && ands.size()==1) {
//				result =(AbstractExpression) ands.get(0);
//			}else 
//				continue;
//			/*
//			 * case1：左操作数为单变量
//			 * case2：左操作数是个按位与操作的表达式，因为表达式类型计算不准备，单独处理
//			 * unsigned short s;
//			 * s&0XB3 应该是是unsigned
//			 * 表达式计算时统一把s转换成int计算
//			 */
//			if((result instanceof ASTid_expression) && isSigned(result)) {
//				addFSMDescription(snode,fsm);
//			}else if(result instanceof ASTand_expression) {
//				ASTUnaryExpression left = (ASTUnaryExpression) result.jjtGetChild(0);
//				ASTUnaryExpression right = (ASTUnaryExpression) result.jjtGetChild(1);
//				if(isSigned(left) && isConstant(right))
//					addFSMDescription(snode,fsm);
//				else if(isSigned(right) && isConstant(left))
//					addFSMDescription(snode,fsm);
//			}
//		}
	    return list;
	}	
	
	private static boolean isSigned(AbstractExpression node) {
		CType type = node.getType();
		if(type == CType_BaseType.intType || type == CType_BaseType.shortType || type == CType_BaseType.longType || type == CType_BaseType.longLongType || type == CType_BaseType.charType) 
			return true;
		else 
			return false;
	}

	private static boolean isConstant(ASTUnaryExpression node) {
		String xpath = "/UnaryExpression/PostfixExpression/PrimaryExpression/Constant";
		List<SimpleNode> exps = StateMachineUtils.getEvaluationResults(node, xpath);
		if(exps!=null && exps.size()==1)
			return true;
		else
			return false;
	}

	private static void addFSMDescription( SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp(" Use Signed Number with Shift Operator. It will lead to unpredictable consequences using shift opeator with signed number.");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("第"+node.getBeginLine()+"行使用了有符号数进行移位操作。\r\n对有符号类型进行移位运算会导致不可预料的后果。");
			}	
		
		list.add(fsminstance);
	}
}
