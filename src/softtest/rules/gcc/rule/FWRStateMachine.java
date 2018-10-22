package softtest.rules.gcc.rule;


import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.interpro.c.InterContext;
import softtest.pretreatment.Pretreatment;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.Type.*;


/**
 * @author maojinyu 
 * Function With Return Statement
 * 函数必须有返回语句/禁止void类型的过程中的return语句带有返回值/有返回值的函数中return必须带有返回值/函数返回类型必须一致
 * (调用返回类)
 */
public class FWRStateMachine {
	
	private enum Type {FIRST_TYPE, SECOND_TYPE, THIRD_TYPE, FOURTH_TYPE}
	//查询所有返回语句
	private static String xpath = ".//JumpStatement[@Image='return']";
	
	private static List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();	
	private static List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
	
	private static CType returnType = null;
	private static String funcName = null;
	
	private static boolean isMultiplicative=false;
	
	public static List<FSMMachineInstance> createFWRMachines(SimpleNode node, FSMMachine fsm){

		if(!(node instanceof ASTFunctionDefinition)) {
			return null;
		}
		
		//如果当前函数在编译库文件、头文件中,跳过
		String filename = node.getFileName();
		if(filename==null || filename.matches(InterContext.INCFILE_POSTFIX))
			return null;
		
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		
		//查询函数返回值类型
		MethodNameDeclaration methodDecl = StateMachineUtils.getMethodDefinition(node);
		if(methodDecl == null ||  methodDecl.isLib()==true)
			return null;
		
		CType_Function funType = (CType_Function)methodDecl.getType();
		returnType=funType.getReturntype();
		funcName = methodDecl.getFullName();
		
		
		
		//如果static void f(){},那么返回值类型为static:void,需要处理一下
		if(returnType instanceof CType_Qualified && returnType.getName().equals("static")) {
			returnType = returnType.getSimpleType();
		}
			
		
		//First_type 如果函数有返回值，但是函数体内无return语句
		if(returnType != CType_BaseType.voidType && evaluationResults.size() == 0) {
			addFSM(node, fsm, Type.FIRST_TYPE);
			return list;
		}
		
		//Second_type 如果函数返回值为void，但是函数体内return语句有返回值
		if(returnType == CType_BaseType.voidType && evaluationResults.size() > 0) {	
			for(SimpleNode snode : evaluationResults) {
				if(snode.jjtGetNumChildren() > 0) {
					addFSM(snode, fsm, Type.SECOND_TYPE);
					return list;
				}
			}
		}
		
		//Third_type 如果函数有返回值，那么函数体内return语句必须也有返回值
		if(returnType != CType_BaseType.voidType && evaluationResults.size() > 0) {
			for(SimpleNode snode : evaluationResults) {
				if(snode.jjtGetNumChildren() == 0) {
					addFSM(snode, fsm, Type.THIRD_TYPE);
					return list;
				}
			}
		}
		
		//Fourth_type 如果函数有返回值，那么函数体内return返回值类型应和函数定义的返回值类型一致
		if(returnType != CType_BaseType.voidType && evaluationResults.size() > 0) {
			for(SimpleNode snode : evaluationResults) {
				if(!(snode.jjtGetChild(0) instanceof ASTExpression))
					continue;
				AbstractExpression retExp = (AbstractExpression) snode.jjtGetChild(0);
				CType type = retExp.getType();
				
			    if((retExp.findChildrenOfType(ASTPrimaryExpression.class)).size()>1)
			    	isMultiplicative=true;
				
			
				//First：特殊处理char* f(){ return NULL; }	  NULL会认为为int型
				if(returnType instanceof CType_Pointer && (retExp.getImage().equals("NULL") || retExp.getImage().equals("0"))) {
					continue;
				}
				
				//Second: 处理return的值为常数，函数声明返回值为无符号数的情况unsigned int f(){ return 1; }
				String Xpath = "./AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression/Constant|./AssignmentExpression/UnaryExpression/UnaryExpression/PostfixExpression/PrimaryExpression/Constant";//说明return后的表达式是个常量
				List<SimpleNode> constants = StateMachineUtils.getEvaluationResults(retExp, Xpath);
				
				if(constants.size()>0) {	
					
					//1： 常量为负数，而返回值为无符号数，需要报告
					if(returnType instanceof CType_BaseType && returnType.getName() != null  && type != null && type.getName() != null && returnType.getName().startsWith("unsigned") && type.getName().equals("int")&&constants.size()>0) {
						String retValue = constants.get(0).getImage();
						int unary = retExp.jjtGetChild(0).jjtGetChild(0).jjtGetNumChildren();
						
						if(unary == 2) {
							addFSM2(snode, fsm, type, returnType);
							continue;
						}
						//2: 如果常数以l/L结束，代表该常量为Long型
						if(retValue != null && (retValue.endsWith("L") || retValue.endsWith("l"))) {					
							type = CType_BaseType.longType;
						}else {
							continue;
						}
					}
					
					//3：由于常数1.0被识别为double类型 
					//处理函数声明返回值为float的情况下， 返回1.0或者1，说明这是误报
					if(returnType instanceof CType_BaseType && (returnType.getName().equals("float") || returnType.getName().equals("double"))) {
							if(type != null && (type.getName().equals("double") || type.getName().equals("int"))) {
								continue;
							}
					}
					
					//4：函数返回值为long型，而return返回int,也算返回类型一致
					if(returnType instanceof CType_BaseType && returnType.getName().equals("long")) {
						if(type != null && type.getName().equals("int")) {
							continue;
						}
					}
				} 
				
				//String Xpath2 = "//AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression";//说明return后的表达式是个变量
				//List<SimpleNode> variables = StateMachineUtils.getEvaluationResults(retExp, Xpath);
				else{
					
				if(!isMatch(type, returnType)) { 
				
					addFSM2(snode, fsm, type, returnType);
				}}
			}
		}	
		
	    return list;
	}	

	

	private static boolean isMatch(CType atype, CType ptype) {
		
		if (atype == null || ptype == null) {			
			return false;
		}		
		if (atype == ptype) {
			return true;
		}
		// can not pass the const argument to the no-const parameter
		if (atype instanceof CType_Qualified && ptype instanceof CType_Qualified) {
			
			CType_Qualified atemp = (CType_Qualified)atype;
			CType_Qualified ptemp = (CType_Qualified)ptype;
			
			if (atemp.getName()==null && ptemp.getName()!=null) {
				return false;
			}
		}
		if (atype instanceof CType_Qualified) {
	
			atype = atype.getSimpleType();
		}
		
		if (ptype instanceof CType_Qualified ) {
		
			ptype = ptype.getSimpleType();
		}
		
		//处理typedef
		if(atype instanceof CType_BaseType && ptype instanceof CType_Typedef){	
			if(isMultiplicative==true)
			return true;		
		}
		
		if (atype instanceof CType_BaseType && ptype instanceof CType_BaseType) {
		if(atype == ptype)
				return true;
		}
		
		// can convert the enum argument into int parameter
		if (atype instanceof CType_Enum && ptype instanceof CType_BaseType) {
			return true;
		}
		// array and pointer
		if (atype instanceof CType_AbstPointer && ptype instanceof CType_AbstPointer) {
			return isMatch(((CType_AbstPointer)atype).getOriginaltype(), ((CType_AbstPointer)ptype).getOriginaltype());
		} 
		
		if (atype == null || ptype == null) {
			return false;
		}

		// 如果当前类型未知，则简单判断是否名字相同
		if ((atype instanceof CType_Unkown && !(ptype instanceof CType_Unkown))
			||(!(atype instanceof CType_Unkown) && ptype instanceof CType_Unkown)) {
			return false;
		}

		if (atype.getName().equals(ptype.getName())) {
			return true;
		}
		return false;
	}

	private static void addFSM(SimpleNode node, FSMMachine fsm, Type type) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		if(type == Type.FIRST_TYPE) {
			
			if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
					fsminstance.setDesp(funcName + " Function with non-void return ,should has return statement. ");
				} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
					fsminstance.setDesp(funcName + " 函数必须有返回语句.");
				}	
		}		
		else if(type == Type.SECOND_TYPE) {
			if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp("Avoid " + funcName + " function with void return type has return statement. ");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("禁止void类型的 " + funcName + " 函数中的return语句带有返回值");
			}
		}	
		else if(type == Type.THIRD_TYPE) {
			if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp(funcName + " Function must has return statement with value. ");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("有返回值的 " + funcName + " 函数中return必须带有返回值");
			}
		}
		
		list.add(fsminstance);
	}
	
	private static void addFSM2(SimpleNode node, FSMMachine fsm, CType type, CType returnType) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
			fsminstance.setDesp(funcName +" Function must has the same return type. ");
		} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
			StringBuffer desp = new StringBuffer(funcName + " 函数返回类型必须一致.");
			if(returnType != null && type != null) {
				desp.append("\r函数定义的返回类型为" + returnType + ", return 返回的类型为 " + type);
			}
			fsminstance.setDesp(desp.toString());
		}
		list.add(fsminstance);
	}
}
