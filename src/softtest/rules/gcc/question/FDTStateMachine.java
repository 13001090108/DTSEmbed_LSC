package softtest.rules.gcc.question;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.ASTAdditiveExpression;
import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTConstant;
import softtest.ast.c.ASTDeclaration;
import softtest.ast.c.ASTMultiplicativeExpression;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTTypeSpecifier;
import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.ASTArgumentExpressionList;
import softtest.ast.c.ASTInitializer;
import softtest.ast.c.ASTPostfixExpression;
import softtest.ast.c.AbstractExpression;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.Type.CType;
import softtest.symboltable.c.Type.CType_BaseType;
/** 
 * @author ssj
 */

public class FDTStateMachine {
	public static List<FSMMachineInstance> createFDTStateMachines(SimpleNode node, FSMMachine fsm)
	{
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> assignResults = null;
		List<SimpleNode> initResults = null;
		List<SimpleNode> ioResults = null;
		List<SimpleNode> parameterResults = null;
			
		
		//隐式类型转换的几种形式：赋值表达式，变量定义，io函数,函数参数
		String assignXpath = ".//Expression//AssignmentExpression[./AssignmentOperator[@Operators='=']]";
		String initXpath =".//Declaration[.//InitDeclarator[./Initializer/AssignmentExpression[not(.//Constant)]]]";
		String ioXpath = ".//PostfixExpression[@Image= 'scanf' or @Image='printf']/ArgumentExpressionList";
		String parameterXpath = ".//PostfixExpression/PrimaryExpression[@Method='true']";
		
		/*赋值表达式的隐式类型转换*/
		assignResults = StateMachineUtils.getEvaluationResults(node, assignXpath);
		Iterator itr = assignResults.iterator();
		
		while(itr.hasNext())
		{
			SimpleNode assignmentExpression= (SimpleNode)itr.next();
			
			if(assignmentExpression.jjtGetNumChildren()!=3){
				continue;
			}
			ASTUnaryExpression  left = (ASTUnaryExpression) assignmentExpression.jjtGetChild(0);
			ASTAssignmentExpression  right = (ASTAssignmentExpression) assignmentExpression.jjtGetChild(2);
			if(left.getType() == null || !(left.getType() instanceof CType_BaseType))
				continue;
			CType_BaseType leftType = (CType_BaseType)left.getType();
			if(!(right.jjtGetChild(0) instanceof ASTAdditiveExpression) && !(right.jjtGetChild(0) instanceof ASTMultiplicativeExpression)){
				addDangerousTransfer(list,assignmentExpression,leftType,right,right.getType(),fsm);
			}else if((right.jjtGetChild(0).jjtGetNumChildren() >= 2) && (right.jjtGetChild(0).jjtGetChild(0) instanceof ASTUnaryExpression)){
				//赋值表达式
				ASTUnaryExpression unaryExp = (ASTUnaryExpression)right.jjtGetChild(0).jjtGetChild(0);
				if(!(unaryExp.getType() instanceof CType_BaseType))
					continue;
				CType_BaseType rightType = (CType_BaseType)unaryExp.getType();
				CType_BaseType tempType = null;
				for(int i = 1; i < right.jjtGetChild(0).jjtGetNumChildren(); i++){
					if(right.jjtGetChild(0).jjtGetChild(i) instanceof ASTUnaryExpression){
						unaryExp = (ASTUnaryExpression)right.jjtGetChild(0).jjtGetChild(i);
						if(!(unaryExp.getType() instanceof CType_BaseType))
							break;
						else{
							tempType = (CType_BaseType)unaryExp.getType();
							int com = compare(rightType,tempType);
							switch(com){
							case 1: break;
							case 0: break;
							case -1:
								rightType = tempType;
								break;
							}
						}
					}
				}
				addDangerousTransfer(list,assignmentExpression,leftType,right,rightType,fsm);
			}
		}
		
		//变量定义的隐式类型转换
		initResults = StateMachineUtils.getEvaluationResults(node, initXpath);
		Iterator itr2 = initResults.iterator();
		
		while(itr2.hasNext())
		{
			ASTDeclaration declaration = (ASTDeclaration)itr2.next();
			ASTInitializer initializer = (ASTInitializer)declaration.getFirstChildOfType(ASTInitializer.class);
			if(declaration.jjtGetNumChildren()!=2){
				continue;
			}
			if( initializer.jjtGetChild(0)==null | !(initializer.jjtGetChild(0) instanceof AbstractExpression))
				continue;
			if(declaration.jjtGetChild(0).jjtGetChild(0) instanceof ASTTypeSpecifier){
				ASTTypeSpecifier left = (ASTTypeSpecifier) declaration.jjtGetChild(0).jjtGetChild(0);
				if(left.getType() == null || !(left.getType() instanceof CType_BaseType))
					continue;
				CType_BaseType leftType = (CType_BaseType)left.getType();
				ASTAssignmentExpression  right = (ASTAssignmentExpression) initializer.jjtGetChild(0);
				addDangerousTransfer(list,initializer,leftType,right,right.getType(),fsm);
			}
		}
		
		
		//io函数的隐式类型转换
		ioResults = StateMachineUtils.getEvaluationResults(node, ioXpath);
		Iterator itr3 = ioResults.iterator();
		
		while(itr3.hasNext())
		{
			ASTArgumentExpressionList ioExpression= (ASTArgumentExpressionList)itr3.next();
			int m = ioExpression.jjtGetNumChildren();
			if( m == 1)
				continue;
			else{
				ASTAssignmentExpression assignmentExpression = (ASTAssignmentExpression)ioExpression.jjtGetChild(0);
				if(assignmentExpression.getFirstChildOfType(ASTConstant.class) != null){
					String format =((ASTConstant) assignmentExpression.getFirstChildOfType(ASTConstant.class)).getImage();
					if(format.length() - 1 > 1)
						format = format.substring(1, format.length()-1).trim();
					CType_BaseType type[] = new CType_BaseType[m - 1];
					for(int i = 0; i < m - 1; i++)
						type[i] = null;
					char form[] = new char[format.length()];
					form = format.toCharArray();
					
					int j = 0;
					for(int i = format.indexOf("%"),count = 0; i < form.length; i = j, count++)
						for(j = i + 1 ; j < form.length; j++){
							if(form[j] == '%' ||  j == form.length-1)
								try{
									{	
										int n;
										if(j == form.length-1)
											n = j - i;
										else
											n = j - i - 1;
										if(n == 0)
										{
											j = format.indexOf("%", j + 1 );
											count--;
											break;
										}
										else if(n == 1)
											switch(form[n + i])
											{
											case 'd': type[count] = new CType_BaseType("int");		break;
											case 'c': type[count]= new CType_BaseType("char");		break;
											case 'f': type[count]= new CType_BaseType("float");		break;
											default:break;
											}
										else 
										{
											for(int k = i + 1;k < i + n; k++)
											{	
												if(count >= type.length || type[count]!= null)
													break;
												switch(form[k])
												{
												case 'l':
													switch(form[k+1])
													{
													case 'd': type[count]= new CType_BaseType("long");	break;
													case 'f': type[count]= new CType_BaseType("double");break;
													case 'l': 
														if(form[k + 2]=='d')
															type[count]= new CType_BaseType("long long");
														else if(form[k + 2]=='f')
															type[count]= new CType_BaseType("long double");
														break;
													}
													break;
												case 'd': type[count]= new CType_BaseType("int") ;		break;
												case 'c': type[count]= new CType_BaseType("char");		break;
												case 'f': type[count]= new CType_BaseType("float");	break;
												default: break;
												}
											}
										}
										break;
									}
								}
							catch(Exception e)
							{
								
							}
						}
					ASTAssignmentExpression exp[] = new ASTAssignmentExpression[m-1];
					for(int i = 0; i < m - 1; i++)
					{
						exp[i] = (ASTAssignmentExpression) ioExpression.jjtGetChild(i+1);
						CType ctp = CType.getOrignType(exp[i].getType());
						if (exp[i].getType() == null || type[i] == null || !(ctp instanceof CType_BaseType))
							continue;
						addDangerousTransfer(list,ioExpression,type[i],exp[i],ctp,fsm);
					}
				}
			 }
		 }
		
		//函数参数传递的隐式类型转换
		parameterResults = StateMachineUtils.getEvaluationResults(node, parameterXpath);
		for (SimpleNode snode : parameterResults) {
			MethodNameDeclaration methodDecl = StateMachineUtils.getMethodNameDeclaration(snode);
			if (methodDecl == null || methodDecl.getScope() == null) {
				continue;
			}
			else {
				List <CType> formalTypeParamList = null;
				ArrayList<CType> actualTypeParamList = new ArrayList<CType>(); 
				List <SimpleNode> actualNodeParamList = null;
				formalTypeParamList = methodDecl.getParams();
				if(snode instanceof ASTPrimaryExpression){
					SimpleNode funDecla = (SimpleNode)snode.getFirstParentOfType(ASTPostfixExpression.class);
					if(funDecla == null)
						continue;
					String Xpath = ".//ArgumentExpressionList/AssignmentExpression";
					actualNodeParamList = StateMachineUtils.getEvaluationResults(funDecla, Xpath);
					if(actualNodeParamList == null )
						continue;
					for(SimpleNode actNode:actualNodeParamList)
						actualTypeParamList.add(((ASTAssignmentExpression)actNode).getType());
				}
				if(actualTypeParamList == null ||actualTypeParamList.isEmpty()||formalTypeParamList.isEmpty()|| formalTypeParamList.size() != actualTypeParamList.size())
					continue;
				Iterator actualItr = actualNodeParamList.iterator();
				Iterator formalItr = formalTypeParamList.iterator();
				while(actualItr.hasNext() && formalItr.hasNext()){
					SimpleNode actualNode = (SimpleNode)actualItr.next();
					CType formal = (CType)formalItr.next();
					CType actual;
					actual = ((ASTAssignmentExpression)actualNode).getType();
					if(actual == null || formal == null)
						continue;
					if(!(actual instanceof CType_BaseType))
						continue;
					if(actual.equals(formal) || actual.getName().equals("void") || formal.getName().equals("void") || 
							actual.getName().equals("bool") || formal.getName().equals("bool") )
						continue ;
					int com =compare(formal,actual);
					switch(com)
					{
					case 1:break;//形参精度高，即低->高赋值，由于大部分情况下都没要危险，所以忽略此种情况
					case 0://同样的精度的 区分unsighed
						if(formal.getName().equals(actual.getName())){
							break;
						}else{
//							由于常数给其他类型的情况很常见，故排除
							String Xpath1 = ".//UnaryExpression/PostfixExpression/PrimaryExpression/Constant";
							String Xpath2 = ".//UnaryExpression/PostfixExpression/PrimaryExpression";
							List<SimpleNode> results1 = null;
							List<SimpleNode> results2 = null;
							results1 = StateMachineUtils.getEvaluationResults(actualNode, Xpath1);
							results2 = StateMachineUtils.getEvaluationResults(actualNode, Xpath2);
							if(((results1 != null) || !(results1.isEmpty())) && results1.size() == results2.size()){
								break;
							}
							addFSM(list,snode,fsm,formal,actual);
							break;
						}
					
					case -1://实参精度高，即高->低赋值
						
						//由于常数给其他类型的情况很常见，故排除
						String Xpath1 = ".//UnaryExpression/PostfixExpression/PrimaryExpression/Constant";
						String Xpath2 = ".//UnaryExpression/PostfixExpression/PrimaryExpression";
						List<SimpleNode> results1 = null;
						List<SimpleNode> results2 = null;
						results1 = StateMachineUtils.getEvaluationResults(actualNode, Xpath1);
						results2 = StateMachineUtils.getEvaluationResults(actualNode, Xpath2);
						if(((results1 != null) || !(results1.isEmpty())) && results1.size() == results2.size()){
							break;
						}

						addFSM(list,snode,fsm,formal,actual); 
						break;
					}
				}
			}
		}
		
		return list;
	}
	
	/**数据类型的比较
	 * 精度相同返回0，left精度高于right返回1,left精度低于right返回-1
	 * (unsigned)char<(unsigned)short<(unsigned)int<
	 * (unsigned)long<float<double<long double
	 */
	private static int compare(CType left,CType right){
		if(left.getName().contains("char")){
			if(right.getName().equals("unsigned char") || right.getName().equals("char"))
				return 0;
			else return -1;
		}
		else if(left.getName().contains("short")){
			if(right.getName().contains("char"))
				return 1;
			else if(right.getName().contains("short"))
				return 0;
			else return 1;
		}
		else if(left.getName().contains("int")){
			if(right.getName().contains("char") || right.getName().contains("short"))
				return 1;
			else if(right.getName().contains("int"))
				return 0;
			else return -1;
		}
		else if(left.getName().equals("long") || left.getName().equals("unsigned long")){
			if(right.getName().contains("float") || right.getName().contains("double"))
				return -1;
			else if(right.getName().equals("long") || right.getName().equals("unsigned long"))
				return 0;
			else return 1;
		}
		else if(left.getName().equals("float")){
			if(right.getName().contains("double"))
				return -1;
			else return 1;
		}
		else if(left.getName().equals("double")){
			if(right.getName().equals("long double"))
				return -1;
			else return 1;
		}
		else if(left.getName().equals("long double"))
			return 1;
		return 1;
	}
	
	
	private static void addDangerousTransfer(List<FSMMachineInstance> list,SimpleNode node, CType_BaseType leftType, ASTAssignmentExpression right, CType righttype,FSMMachine fsm){
		
		if( !(righttype instanceof CType_BaseType) || righttype == null)
			return;
		CType_BaseType rightType = (CType_BaseType)righttype;
		if(leftType.equals(rightType) || leftType.getName().equals("void") || rightType.getName().equals("void") || 
				leftType.getName().equals("bool") || rightType.getName().equals("bool") )
			return ;
		int com =compare(leftType,rightType);
		switch(com)
		{
		case 1:break;//左侧精度高，即低->高赋值，由于大部分情况下都没要危险，所以忽略此种情况
		case 0://同样的精度的 区分unsighed
			
			if(leftType.getName().equals(rightType.getName())){
				break;
			}else{
//				由于常数给其他类型的情况很常见，故排除
				String Xpath1 = ".//UnaryExpression/PostfixExpression/PrimaryExpression/Constant";
				String Xpath2 = ".//UnaryExpression/PostfixExpression/PrimaryExpression";
				List<SimpleNode> results1 = null;
				List<SimpleNode> results2 = null;
				results1 = StateMachineUtils.getEvaluationResults(right, Xpath1);
				results2 = StateMachineUtils.getEvaluationResults(right, Xpath2);
				if(((results1 != null) || !(results1.isEmpty())) && results1.size() == results2.size()){
					break;
				}else{
					addFSM(list,node,fsm,leftType,rightType);
					break;
				}
			}
			
		case -1://右侧精度高，即高->低赋值
			
			//由于常数给其他类型的情况很常见，故排除
			String Xpath1 = ".//UnaryExpression/PostfixExpression/PrimaryExpression/Constant";
			String Xpath2 = ".//UnaryExpression/PostfixExpression/PrimaryExpression";
			List<SimpleNode> results1 = null;
			List<SimpleNode> results2 = null;
			results1 = StateMachineUtils.getEvaluationResults(right, Xpath1);
			results2 = StateMachineUtils.getEvaluationResults(right, Xpath2);
			if(((results1 != null) || !(results1.isEmpty())) && results1.size() == results2.size()){
				break;
			}
							
			addFSM(list,node,fsm,leftType,rightType);
			break;
		
		}
	}
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm,CType left,CType right) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp(" FaultDataTransform :"+"Type '"+right.getName()+"' assigned to "+"type "+left.getName()+",Obscure data transforming between deferent type of data may lead to error of data");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("第"+node.getBeginLine()+"行数据类型转换错误: "+right.getName()+"类型转换成"+left.getName()+"类型，不同数据类型之间的隐式转换可能会使数据发生错误。");
			}	
		list.add(fsminstance);
	
	}
}
