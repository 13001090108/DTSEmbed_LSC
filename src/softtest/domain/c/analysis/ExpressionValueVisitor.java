package softtest.domain.c.analysis;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.DomainType;
import softtest.domain.c.interval.DoubleDomain;
import softtest.domain.c.interval.IntegerDomain;
import softtest.domain.c.interval.IntegerInterval;
import softtest.domain.c.interval.PointerDomain;
import softtest.domain.c.interval.PointerValue;
import softtest.domain.c.symbolic.DoubleFactor;
import softtest.domain.c.symbolic.Expression;
import softtest.domain.c.symbolic.IntegerFactor;
import softtest.domain.c.symbolic.SymbolFactor;
import softtest.fsm.c.FSMMachineInstance;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.Method;
import softtest.interpro.c.Variable;
import softtest.summary.c.MethodFeature;
import softtest.summary.c.MethodPostCondition;
import softtest.summary.c.MethodSummary;
import softtest.symboltable.c.*;
import softtest.symboltable.c.Type.*;

/**modified by zys 	2010.7.26
 * 在一些叠加表达式计算时（如LogicalORExpression，AdditiveExpression....),其原理是先计算最左表达式的值，
 * 然后依次计算后续表达式的值，根据左右值之间的操作符计算出中间结果，把中间结果向后续的计算进行传递，得到最终表达式的值；
 * 
 * 如果在计算过程中某一环节出现左右值为NULL的情况，则： 
 * 1、首先计算完后续的表达式，以防止其中包含变量的修改（如if(i*k>0 && i++>5),如果左值i*k>0计算不出来，则继续计算&&右侧表达式，
 * 		防止漏掉其中的i++运算；
 * 2、在所有表达式都计算完毕后，为整个表达式赋一个全区间
 * 3、以上两步骤的代码通过捕获异常的方式实现
 *  */
public class ExpressionValueVisitor extends CParserVisitorAdapter {
	/**
	 * ASTAdditiveExpression
	 * ASTANDExpression
	 * ASTArgumentExpressionList
	 * ASTAssignmentExpression
	 * ASTCastExpression
	 * ASTConditionalExpression
	 * ASTConstant
	 * ASTConstantExpression
	 * ASTEqualityExpression
	 * ASTExpression
	 * ASTFieldId
	 * ASTInclusiveORExpression
	 * ASTLogicalANDExpression
	 * ASTLogicalORExpression
	 * ASTPostfixExpression
	 * ASTPrimaryExpression
	 * ASTRelationalExpression
	 * ASTShiftExpression
	 * ASTUnaryExpression
	 */	
	public Object visit(ASTAdditiveExpression node, Object data) {
		ExpressionVistorData expdata=(ExpressionVistorData)data;
		node.jjtGetChild(0).jjtAccept(this, expdata);
		Expression leftvalue=expdata.value;
		Expression rightvalue=null;
		try{	
			//从左到右进行符号计算
			for (int i = 1; i < node.jjtGetNumChildren(); i++) {
				Node c = node.jjtGetChild(i);
				expdata.value = null;
				c.jjtAccept(this, expdata);
				rightvalue = expdata.value;
				String operator = node.getOperatorType().get(i-1);
				if(leftvalue==null || rightvalue==null)
					throw new MyNullPointerException("AdditiveExpression Value NULL in(.i) "+node.getBeginFileLine());
				if (operator.equals("+")){
					leftvalue=leftvalue.add(rightvalue);
				}else{
					leftvalue=leftvalue.sub(rightvalue);
				}
			}
		}catch(MyNullPointerException e){
			super.visit(node,expdata);
			SymbolFactor sym=SymbolFactor.genSymbol(CType_BaseType.getBaseType("double"));
			expdata.currentvex.addSymbolDomain(sym, DoubleDomain.getFullDomain());
			leftvalue=new Expression(sym);
			expdata.value=leftvalue;
			return data;
		}
		
		expdata.value=leftvalue;
		return data;
	}
	
	public Object visit(ASTANDExpression node, Object data) {
		return dealBinaryBitOperation(node,data,"&");
	}
	
	public Object visit(ASTArgumentExpressionList node, Object data) {
		//在ASTPostfixExpression中统一处理
		return super.visit(node, data);
	}
	//modified by zhouhb
	public Object visit(ASTInitDeclarator node, Object data) {
		ExpressionVistorData expdata=(ExpressionVistorData)data;
		ASTDeclarator declarator = null;
		if(node.jjtGetChild(0) instanceof ASTDeclarator){
			declarator=(ASTDeclarator)node.jjtGetChild(0);
		}else if(node.jjtGetChild(1) instanceof ASTDeclarator){
			declarator=(ASTDeclarator)node.jjtGetChild(1);
		}
		NameDeclaration decl=declarator.getFinalDirectDeclarator().getDecl();
		//不处理结构体相关信息
		//add by zhouhb 2010/8/19
		//zys 2011.6.23	为什么这样处理？ File *fp=null;就不能处理了？
//		if(!Config.Field){
//			if(decl!=null){
//				if(decl.getType() instanceof CType_Array && (((CType_Array)decl.getType()).getOriginaltype() instanceof CType_Struct||((CType_Array)decl.getType()).getOriginaltype() instanceof CType_Pointer)||
//						decl.getType() instanceof CType_Struct||decl.getType() instanceof CType_Pointer && (((CType_Pointer)decl.getType()).getOriginaltype() instanceof CType_Struct||((CType_Pointer)decl.getType()).getOriginaltype() instanceof CType_Typedef||((CType_Pointer)decl.getType()).getOriginaltype() instanceof CType_Pointer))
//					return data;	
//			}
//		}
		if(node.jjtGetNumChildren()==1){
			if(node.getType() instanceof CType_Pointer)	{
				SymbolFactor sym=SymbolFactor.genSymbol(node.getType());
				PointerDomain p=new PointerDomain();
				expdata.currentvex.addSymbolDomain(sym, p);
				expdata.value=new Expression(sym);
			}else if(node.getType() instanceof CType_Array){
				SymbolFactor sym=SymbolFactor.genSymbol(node.getType());
				PointerDomain p=new PointerDomain();
				//modified by zhouhb 2010/7/23
				//修改了数组初始化时关联指针的属性为NULL
				p.setValue(PointerValue.NOTNULL);
				//modified by zhouhb 2010/6/22
				//增加了利用全局变量初始化数组的功能 eg.char[a]
				ASTConstantExpression constant=(ASTConstantExpression)node.getFirstChildOfType(ASTConstantExpression.class);
				//判断是否为char a[]这种未定义维度的数组声明
				if(constant!=null){
					constant.jjtAccept(this, data);	
					if(expdata.value!=null)
					{
						Domain dd=expdata.value.getDomain(expdata.currentvex.getSymDomainset());					
						IntegerDomain size=IntegerDomain.castToIntegerDomain(dd);
						//判断数组维数是否为函数参数
						if(size!=null){
						int arraySize=(int)size.getMin();	
						p.offsetRange=new IntegerDomain(0,arraySize*((CType_Array)node.getType()).getOriginaltype().getSize()-1);
						//p.AllocType=CType_AllocType.stackType;
						if(p.Type.contains(CType_AllocType.NotNull)){
							p.Type.remove(CType_AllocType.NotNull);
						}
						p.Type.add(CType_AllocType.stackType);
						}
					}
				}
				expdata.currentvex.addSymbolDomain(sym, p);
				expdata.value=new Expression(sym);
				expdata.currentvex.addValue((VariableNameDeclaration)decl, expdata.value);
			}
				return data;
		}
		if(decl instanceof VariableNameDeclaration){
			VariableNameDeclaration v=(VariableNameDeclaration)decl;
			node.jjtGetChild(1).jjtAccept(this, expdata);
			if(node.jjtGetChild(1) instanceof ASTInitializer){
				if(node.getType() instanceof CType_Array){		
					//处理数组初始化长度eg.int a[5]={3,3,4}
					//modified by zhouhb 2010/7/21
					
					if(node.containsChildOfType(ASTInitializerList.class)){
						int num=((ASTInitializerList)node.getFirstChildOfType(ASTInitializerList.class)).jjtGetNumChildren();
						PointerDomain p=new PointerDomain();
						p.offsetRange=new IntegerDomain(0,((CType_Array)node.getType()).getDimSize()-1);
						p.allocRange=new IntegerDomain(num,num);
						//p.AllocType=CType_AllocType.stackType;
						if(num>0)
						{
							p.setValue(PointerValue.NOTNULL);
						}
						if(p.Type.contains(CType_AllocType.NotNull)){
							p.Type.remove(CType_AllocType.NotNull);
						}
						p.Type.add(CType_AllocType.stackType);
						SymbolFactor sym=SymbolFactor.genSymbol(node.getType());
						expdata.value=new Expression(sym);
						expdata.currentvex.addSymbolDomain(sym, p);
						expdata.currentvex.addValue(v, expdata.value);
						Expression exp=expdata.value;
						
						ExpressionVistorData expdata1=expdata;
						CType_Array typeArr=(CType_Array)node.getType();
						//只处理一维数组
						for(int i=0;i<num&&i<=Config.MaxArray&&typeArr.getDimSize()==typeArr.getMemNum();i++)
						{
							String arrImage=v.getImage()+"["+i+"]";
							NameDeclaration decl0=Search.searchInVariableAndMethodUpward(arrImage, node.getScope());
							if(decl0!=null&&decl0 instanceof VariableNameDeclaration)
							{
								VariableNameDeclaration arrV=(VariableNameDeclaration)decl0;
								ASTInitializerList aList=(ASTInitializerList)node.getFirstChildOfType(ASTInitializerList.class);
								((AbstractExpression)aList.jjtGetChild(i).jjtGetChild(0)).jjtAccept(this, expdata1);
								
								if(expdata1.value==null)
									expdata1.value=new Expression(SymbolFactor.genSymbol(arrV.getType(), arrV.getImage()));
								expdata1.currentvex.addValue(arrV, expdata1.value);									
							}							
						}
						expdata.value=exp;
					}else{
						Expression e=expdata.value;
						PointerDomain p=(PointerDomain)e.getDomain(expdata.currentvex.getSymDomainset());
						if(p!=null){
							p.offsetRange=new IntegerDomain(0,((CType_Array)node.getType()).getDimSize()-1);
							//p.AllocType=CType_AllocType.stackType;
							if(p.Type.contains(CType_AllocType.NotNull)){
								p.Type.remove(CType_AllocType.NotNull);
							}
							p.Type.add(CType_AllocType.stackType);
							SymbolFactor temp=(SymbolFactor)e.getSingleFactor();
							expdata.currentvex.addSymbolDomain(temp, p);
						}
					}
				}//add by zhouhb 2010/8/16
				 //修改了空指针赋值使用
				else if(node.getType() instanceof CType_Pointer){
					if(node.containsChildOfType(ASTConstant.class)&&!node.containsParentOfType(ASTEqualityExpression.class)&&((ASTConstant)node.getFirstChildOfType(ASTConstant.class)).getImage().equals("0")){
						//处理空指针NULL
						SymbolFactor p=SymbolFactor.genSymbol(node.getType());
						PointerDomain pDomain=new PointerDomain();
						pDomain.offsetRange.intervals.clear();
						//pDomain.AllocType=CType_AllocType.Null;
						pDomain.Type.add(CType_AllocType.Null);
						pDomain.setValue(PointerValue.NULL);
						expdata.currentvex.addSymbolDomain(p, pDomain);
						expdata.value=new Expression(p);
					}
				}
				if(expdata.sideeffect && expdata.currentvex != null) {
					if(expdata.value==null)
						expdata.value=new Expression(SymbolFactor.genSymbol(decl.getType(), decl.getImage()));
					expdata.currentvex.addValue(v, expdata.value);				
				}
			}
		}
		return data;
	}
	
	public Object visit(ASTAssignmentExpression node, Object data) {
		ExpressionVistorData expdata=(ExpressionVistorData)data;
		//modified by zhouhb
		SimpleNode postfix=(SimpleNode)node.jjtGetParent().jjtGetParent();	
		if(postfix.getImage().equals("calloc")&&!(node.containsChildOfType(ASTConstant.class)))
			return data;
		if(node.jjtGetNumChildren()==1){
			node.jjtGetChild(0).jjtAccept(this, expdata);
		} 
		//增加对 func(int,a)即参数第一个其实是参数类型，第二个是真正实参的支持
		else if(node.jjtGetNumChildren()==2) {
			node.jjtGetChild(1).jjtAccept(this, expdata);
		}else {
			Expression leftvalue,rightvalue;
			SimpleNode firstchild=(SimpleNode)node.jjtGetChild(0);
			SimpleNode secondchild=(SimpleNode)node.jjtGetChild(1);
			SimpleNode thirdchild=(SimpleNode)node.jjtGetChild(2);
			thirdchild.jjtAccept(this, expdata);
			rightvalue=expdata.value;
			if(rightvalue==null)
				return data;
			if(secondchild.getOperatorType().get(0).equals("=")){
				firstchild.jjtAccept(this, expdata);
				//add by zhouhb 2010/8/16
				 //修改了空指针赋值使用
				if(node.getType() instanceof CType_Pointer){
					//add by zhouhb 2010/11/18
					//屏蔽指针数组
					ASTPrimaryExpression pri=(ASTPrimaryExpression)firstchild.getFirstChildOfType(ASTPrimaryExpression.class);
					if(pri.getType() instanceof CType_Array){
						
						/**dongyk 2012.4.11 增加对指针数组(即数组元素是指针类型)的处理*/
						IntegerDomain domain=Domain.castToIntegerDomain(rightvalue.getDomain(expdata.currentvex.getSymDomainset()));
						//ASTConstant ac=(ASTConstant)thirdchild.getFirstChildOfType(ASTConstant.class);
						//if(ac!=null)
						//{
							//String image=ac.getImage();
							if(domain!=null)
							{
								PointerDomain pDomain=new PointerDomain();
								if(domain.getMin()<1)
								{
									pDomain.offsetRange.intervals.clear();
									//pDomain.AllocType=CType_AllocType.Null;
									pDomain.Type.add(CType_AllocType.Null);
									pDomain.setValue(PointerValue.NULL);
								}
								if(domain.getMin()>0)
								{
									pDomain.Type.add(CType_AllocType.NotNull);
									pDomain.setValue(PointerValue.NOTNULL);
								}
								//将符号运算表达式和整型表达式均转化为单符号（不知道为什么空指针会计算出上述两种情况）
								if(expdata.value==null||expdata.value.getSingleFactor()==null||
										(expdata.value.getSingleFactor()!=null&&
												expdata.value.getSingleFactor() instanceof IntegerFactor)){
									expdata.value=new Expression(SymbolFactor.genSymbol(node.getType()));
								}
								expdata.currentvex.addSymbolDomain((SymbolFactor)expdata.value.getSingleFactor(), pDomain);
								rightvalue=expdata.value;
							}
						//}
						
						//return data;
					}
					if(node.containsChildOfType(ASTConstant.class)&&
							!node.containsParentOfType(ASTEqualityExpression.class)){
						
						IntegerDomain domain=Domain.castToIntegerDomain(rightvalue.getDomain(expdata.currentvex.getSymDomainset()));
											
						ASTConstant ac=(ASTConstant)node.getFirstChildOfType(ASTConstant.class);
						String image=ac.getImage();
						if(domain!=null&&domain.getMin()<1&&image.equals("0"))
						{
						
							PointerDomain pDomain=new PointerDomain();
							pDomain.offsetRange.intervals.clear();
							//pDomain.AllocType=CType_AllocType.Null;
							pDomain.Type.add(CType_AllocType.Null);
							pDomain.setValue(PointerValue.NULL);
							//将符号运算表达式和整型表达式均转化为单符号（不知道为什么空指针会计算出上述两种情况）
							if(expdata.value==null||expdata.value.getSingleFactor()==null||
									(expdata.value.getSingleFactor()!=null&&
											expdata.value.getSingleFactor() instanceof IntegerFactor)){
								expdata.value=new Expression(SymbolFactor.genSymbol(node.getType()));
							}
							expdata.currentvex.addSymbolDomain((SymbolFactor)expdata.value.getSingleFactor(), pDomain);
							rightvalue=expdata.value;
						}
					}
				}
				expdata.value=rightvalue;
			}else if(secondchild.getOperatorType().get(0).equals("*=")){
				firstchild.jjtAccept(this, expdata);
				leftvalue=expdata.value;
				if(leftvalue!=null)
				{
					expdata.value=leftvalue.mul(rightvalue);
				}
			}else if(secondchild.getOperatorType().get(0).equals("/=")){
				firstchild.jjtAccept(this, expdata);
				leftvalue=expdata.value;
				if(leftvalue!=null)
					expdata.value=leftvalue.div(rightvalue);
			}else if(secondchild.getOperatorType().get(0).equals("+=")){
				firstchild.jjtAccept(this, expdata);
				leftvalue=expdata.value;
				if(leftvalue!=null){
					expdata.value=leftvalue.add(rightvalue);
				}
			}else if(secondchild.getOperatorType().get(0).equals("-=")){
				firstchild.jjtAccept(this, expdata);
				leftvalue=expdata.value;
				if(leftvalue!=null){
					expdata.value=leftvalue.sub(rightvalue);
				}
			}else {
				node.jjtGetChild(0).jjtAccept(this, expdata);
				leftvalue=expdata.value;
				if(leftvalue!=null){
					IntegerDomain i1 = Domain.castToIntegerDomain(leftvalue.getDomain(expdata.currentvex.getSymDomainset()));
					IntegerDomain i2 = Domain.castToIntegerDomain(rightvalue.getDomain(expdata.currentvex.getSymDomainset()));
					// 如果不能确定计算出值，直接产生一个抽象取值未定的符号
					if (i1!=null&&i2!=null&&i1.isCanonical() && i2.isCanonical()) {
						long temp = 0;
						if(secondchild.getOperatorType().get(0).equals("&=")){
							temp=i1.getMin()& i2.getMin();
						}else if(secondchild.getOperatorType().get(0).equals("|=")){
							temp=i1.getMin()| i2.getMin();
						}else if(secondchild.getOperatorType().get(0).equals("^=")){
							temp=i1.getMin() ^ i2.getMin();
						}else if(secondchild.getOperatorType().get(0).equals(">>=")){
							temp=i1.getMin() >> i2.getMin();
						}else if(secondchild.getOperatorType().get(0).equals("<<=")){
							temp=i1.getMin() << i2.getMin();
						}else if(secondchild.getOperatorType().get(0).equals("%=")){
							temp=i1.getMin() % i2.getMin();
						}
						expdata.value = new Expression(new IntegerFactor(temp));
					} else {
						expdata.value = new Expression(SymbolFactor.genSymbol(CType_BaseType.getBaseType("int")));
					}
				}
				
			}
			ASTPrimaryExpression p = (ASTPrimaryExpression) firstchild.getSingleChildofType(ASTPrimaryExpression.class);
			if(p!=null){
				VariableNameDeclaration v = p.getVariableDecl();
				if (v != null && expdata.sideeffect && expdata.currentvex != null&&expdata.value!=null) {
					expdata.currentvex.addValue(v, expdata.value);
				}
			}
			if(Config.Field){
				//用于实现结构体成员敏感的计算		
				ASTPostfixExpression po=(ASTPostfixExpression) firstchild.getSingleChildofType(ASTPostfixExpression.class);
				if(po!=null){
					
					ASTPrimaryExpression pri=(ASTPrimaryExpression)po.getFirstDirectChildOfType(ASTPrimaryExpression.class);
					VariableNameDeclaration vPri=pri.getVariableDecl();
					
					if(vPri!=null&&(vPri.getType() instanceof CType_Array||vPri.getType() instanceof CType_Pointer))
					{
						for(int i=0;i<expdata.arrayIndex.size();i++)
						{
							int vIndex=expdata.arrayIndex.get(i).intValue();
							String image=pri.getImage()+"["+vIndex+"]";
							NameDeclaration declArrar=Search.searchInVariableAndMethodUpward(image, node.getScope());
							if(declArrar!=null&& expdata.sideeffect && expdata.currentvex != null&&expdata.value!=null)
							{
								VariableNameDeclaration vArray=(VariableNameDeclaration)declArrar;
								Expression arrExpression=expdata.currentvex.getValue(vArray);
								if(arrExpression==null)
								{
									expdata.currentvex.addValue(vArray, expdata.value);
								}
								else
								{
									Domain arrDomain=arrExpression.getDomain(expdata.currentvex.getSymDomainset());
									Domain rightDomain=expdata.value.getDomain(expdata.currentvex.getSymDomainset());
									Domain newDomain=Domain.union(arrDomain, rightDomain, vArray.getType());
									
									SymbolFactor sym=SymbolFactor.genSymbol(vArray.getType());
									expdata.currentvex.addSymbolDomain(sym, newDomain);								
									expdata.currentvex.getValueSet().addValue(vArray, new Expression(sym));
								}
							}
							
						}
					}
				/**							
					VariableNameDeclaration v = po.getVariableDecl();
					if (v != null && expdata.sideeffect && expdata.currentvex != null&&expdata.value!=null) {
						expdata.currentvex.addValue(v, expdata.value);
					}*/
				}
				//用于实现多级指针成员敏感的计算
				ASTUnaryExpression un=(ASTUnaryExpression) firstchild.getSingleChildofType(ASTUnaryExpression.class);
				if(un!=null){
					VariableNameDeclaration v = un.getVariableDecl();
					if (v != null && expdata.sideeffect && expdata.currentvex != null&&expdata.value!=null) {
						expdata.currentvex.addValue(v, expdata.value);
					}
				}
			}
		}
		return data;
	}
	
	public Object visit(ASTCastExpression node, Object data) {
		super.visit(node, data);
		//由于新的编译环境将NULL编译为0，有时为(void *)0，故修改
		//add by zhouhb
		//对于"=="表达式的处理时不产生空指针对应符号
		ExpressionVistorData expdata=(ExpressionVistorData)data;
		//强制类型转换可能会引起现有版本不能分析的类型的错误区间信息，在此屏蔽
		//add by zhouhb 2010/8/30
		ASTTypeName type=(ASTTypeName)node.getFirstChildOfType(ASTTypeName.class);//
		if(type!=null){
			CType cast=type.getType();
			if(cast instanceof CType_Pointer&&!(((CType_Pointer)cast).getOriginaltype() instanceof CType_BaseType))
			{
				return data;
			}
		}
		
		if(node.jjtGetNumChildren()==2
				&&node.containsChildOfType(ASTConstant.class)
				&&!node.containsParentOfType(ASTEqualityExpression.class)){
			//处理空指针NULL
			Expression leftvalue=expdata.value;
			IntegerDomain domain=null;
			if(leftvalue!=null){
				domain = Domain.castToIntegerDomain(leftvalue.getDomain(expdata.currentvex.getSymDomainset()));
			}	
			if(domain==null||(domain!=null&&domain.getMin()<1&&
					((ASTConstant)node.getFirstChildOfType(ASTConstant.class)).getImage().equals("0")&&
					(((ASTTypeName)node.getFirstChildOfType(ASTTypeName.class)).getType() instanceof CType_Pointer))){
				SymbolFactor p=SymbolFactor.genSymbol(node.getType());
				PointerDomain pDomain=new PointerDomain();
				pDomain.offsetRange.intervals.clear();
				//pDomain.AllocType=CType_AllocType.Null;
				pDomain.Type.add(CType_AllocType.Null);
				pDomain.setValue(PointerValue.NULL);
				expdata.currentvex.addSymbolDomain(p, pDomain);
				expdata.value=new Expression(p);
				}
		}
		return data;
	}
	
	public Object visit(ASTConditionalExpression node, Object data) {
		super.visit(node, data);
		//由于void ConditionalExpression() #ConditionalExpression(>1): {}所以不会生成单支树，所以代码冗余了
		if (node.jjtGetNumChildren() == 1) {
			throw new RuntimeException("ASTConditionalExpression can't generate single child");
			//liuli:条件运算符的第二个表达式可以为空，像c = (++a ? : b);这种情况
		}else if(node.jjtGetNumChildren() == 2){
			Expression firstvalue,thirdvalue;
			ExpressionVistorData expdata=(ExpressionVistorData)data;
			
			SimpleNode firstchild=(SimpleNode)node.jjtGetChild(0);
			firstchild.jjtAccept(this, expdata);
			firstvalue=expdata.value;
			expdata.value = null;		
			SimpleNode thirdchild = (SimpleNode) node.jjtGetChild(1);
			thirdchild.jjtAccept(this, expdata);
			thirdvalue = expdata.value;
			
			IntegerDomain i = Domain.castToIntegerDomain(firstvalue.getDomain(expdata.currentvex.getSymDomainset()));
			if (i != null ) {
				if (i.isCanonical()&& i.getMin() == 0) {
					expdata.value = thirdvalue;
				} else if(!i.contains(0)){
					expdata.value = new Expression(1);//若第二个参数为空，缺省值为1
				}
				return data;
			}
		
			//产生一个新的符号，域为两者的并
			CType type=node.getType();
			SymbolFactor sym=SymbolFactor.genSymbol(type);
			if(type!=null){
				Domain d1=Domain.castToType(new IntegerDomain(1,1), type);
				Domain d2=Domain.castToType(thirdvalue.getDomain(expdata.currentvex.getSymDomainset()), type);
				expdata.currentvex.addSymbolDomain(sym, Domain.union(d1, d2, type));							
			}
			expdata.value=new Expression(sym);
		}else {
			Expression firstvalue,secondvalue,thirdvalue;
			ExpressionVistorData expdata=(ExpressionVistorData)data;
			
			SimpleNode firstchild=(SimpleNode)node.jjtGetChild(0);
			firstchild.jjtAccept(this, expdata);
			firstvalue=expdata.value;
			expdata.value = null;
			
			SimpleNode secondchild=(SimpleNode)node.jjtGetChild(1);
			secondchild.jjtAccept(this, expdata);
			secondvalue=expdata.value;
			expdata.value = null;
			
			SimpleNode thirdchild = (SimpleNode) node.jjtGetChild(2);
			thirdchild.jjtAccept(this, expdata);
			thirdvalue = expdata.value;

			IntegerDomain i=null;
			Domain d=null;
			if(firstvalue!=null&&expdata!=null&&expdata.currentvex!=null)
			{
				d=firstvalue.getDomain(expdata.currentvex.getSymDomainset());			
			}
			if(d!=null)
				i= Domain.castToIntegerDomain(d);
			if (i != null ) {
				if (i.isCanonical()&& i.getMin() == 0) {
					expdata.value = thirdvalue;
				} else if(i.isCanonical()&& i.getMax() == 1){
					expdata.value = secondvalue;
				}else
				{
					expdata.value=thirdvalue;
					
				}
				return data;
			}
		
			//产生一个新的符号，域为两者的并
			CType type=node.getType();
			SymbolFactor sym=SymbolFactor.genSymbol(type);
			if(type!=null && secondvalue!=null && thirdvalue!=null){
				Domain d1=Domain.castToType(secondvalue.getDomain(expdata.currentvex.getSymDomainset()), type);
				Domain d2=Domain.castToType(thirdvalue.getDomain(expdata.currentvex.getSymDomainset()), type);
				expdata.currentvex.addSymbolDomain(sym, Domain.union(d1, d2, type));
			}
			expdata.value=new Expression(sym);
		}
		return data;
	}
	
	public Object visit(ASTConstant node, Object data) {
		ExpressionVistorData expdata = (ExpressionVistorData) data;
		String image = node.getImage();
		if (image.startsWith("\"") || image.startsWith("L\"") 
				||image.equals("__FUNCTION__") ||image.equals("__PRETTY_FUNCTION__") ||image.equals("__func__")) {//增加对L"abcd"形式的字符串赋值形式的处理
			PointerDomain p=new PointerDomain();
			p.offsetRange=new IntegerDomain(0,image.length()-2);
			p.allocRange=new IntegerDomain(image.length()-1,image.length()-1);
			//p.AllocType=CType_AllocType.staticType;
			if(p.Type.contains(CType_AllocType.NotNull)){
				p.Type.remove(CType_AllocType.NotNull);
			}
			p.Type.add(CType_AllocType.staticType);
			p.setElementtype(CType_BaseType.getBaseType("char"));
			p.setLength(new Expression(image.length()+1));
			p.setValue(PointerValue.NOTNULL);
			SymbolFactor sym=SymbolFactor.genSymbol(node.getType());
			expdata.currentvex.addSymbolDomain(sym, p);
			expdata.value=new Expression(sym);
		}else if (( image.startsWith("L\'") ||  image.startsWith("\'") )&& !(image.startsWith("\'\\x")) ) {
			if (image.length() <= 2) {
				throw new RuntimeException("This is not a legal character");
			}
			if( image.startsWith("L\'")){
				image = image.substring(1, image.length());
			}
			//liuli:2010.7.23处理类似int i='DpV!';语句
			if(image.length()>3){
				if(image.startsWith("\'") && image.endsWith("\'")){
					if(!image.startsWith("\'\\")){
						SymbolFactor sym=SymbolFactor.genSymbol(node.getType());
						IntegerDomain p=new IntegerDomain();
						expdata.currentvex.addSymbolDomain(sym, p);
						expdata.value=new Expression(sym);
						return data;
					}
				}else{
					throw new RuntimeException("This is not a legal character");
				}
			}
			int count = 1;
			int secondChar = image.charAt(count++);
			int nextChar = image.charAt(count++);
			char value = (char) secondChar;
			if (secondChar == '\\') {
				switch (nextChar) {
				case 'b':
					value = '\b';
					break;
				case 't':
					value = '\t';
					break;
				case 'n':
					value = '\n';
					break;
				case 'f':
					value = '\f';
					break;
				case 'r':
					value = '\r';
					break;
				case '\"':
					value = '\"';
					break;
				case '\'':
					value = '\'';
					break;
				case '\\':
					value = '\\';
					break;
				case 'a':						
					break;
				case 'v':					
					break;
				case 'e':
					break;
				case '?':					
					break;
				default: // octal (well-formed: ended by a ' )
					if ('0' <= nextChar && nextChar <= '7') {
						int number = nextChar - '0';
						if (count >= image.length()) {
							throw new RuntimeException("This is not a legal character");
						}
						nextChar = image.charAt(count);
						if (nextChar != '\'') {
							count++;
							if (!('0' <= nextChar && nextChar <= '7')) {
								throw new RuntimeException("This is not a legal character");
							}
							number = (number * 8) + nextChar - '0';
							if (count >= image.length()) {
								throw new RuntimeException("This is not a legal character");
							}
							nextChar = image.charAt(count);
							if (nextChar != '\'') {
								count++;
								if (!('0' <= nextChar && nextChar <= '7')) {
									throw new RuntimeException("This is not a legal character");
								}
								number = (number * 8) + nextChar - '0';
							}
						}
						value = (char) number;
					} else {
						throw new RuntimeException("This is not a legal character");
					}
				}
				if (count >= image.length()) {
					System.out.println("cnt:" + count + "  " + image + image.length());
					throw new RuntimeException("This is not a legal character");
				}
				nextChar = image.charAt(count++);
			}
			if (nextChar != '\'') {
				throw new RuntimeException("This is not a legal character");
			}
			if(secondChar == '\\'){
				int value_temp = image.charAt(count-2);
				switch(value_temp){
				case 'a':
					expdata.value=new Expression(new IntegerFactor(007));
					break;
				case 'v':
					expdata.value=new Expression(new IntegerFactor(011));
					break;
				case '?':
					expdata.value=new Expression(new IntegerFactor(063));
					break;
				default:
					expdata.value=new Expression(new IntegerFactor(value));
				}
			}else{
				expdata.value=new Expression(new IntegerFactor(value));
			}
			

		} else {
			if(image.startsWith("\'\\x")){
				image = image.replace("\'", "");
				image = image.replace("\\x", "0x");
			}
			boolean isInteger = false;
			
			if (image.endsWith("l") || image.endsWith("L")){
				image = image.substring(0, image.length() - 1);//以L结尾
				if(image.endsWith("l") || image.endsWith("L")){
					image = image.substring(0, image.length() - 1);//以LL结尾
					if(image.endsWith("u") || image.endsWith("U")){
						image = image.substring(0, image.length() - 1);//以ULL结尾
					}
				}else if(image.endsWith("u") || image.endsWith("U")){
					image = image.substring(0, image.length() - 1);//以UL结尾
				}
			}else if(image.endsWith("u") || image.endsWith("U")){
				image = image.substring(0, image.length() - 1);//以U结尾
				if(image.endsWith("l") || image.endsWith("L")){
					image = image.substring(0, image.length() - 1);//以LU结尾
					if(image.endsWith("l") || image.endsWith("L")){
						image = image.substring(0, image.length() - 1);//以LLU结尾
					}
				}
			}				
			
			char[] source = image.toCharArray();
			int length = source.length;
			long intValue = 0;
			double doubleValue = 0;
			long computeValue = 0L;
			try {
				if (source[0] == '0') {
					if (length == 1) {
						computeValue = 0;
					} else {
						final int shift, radix;
						int j;
						if ((source[1] == 'x') || (source[1] == 'X')) {
							shift = 4;
							j = 2;
							radix = 16;
						} else {
							shift = 3;
							j = 1;
							radix = 8;
						}
						while (source[j] == '0') {
							j++; // jump over redondant zero
							if (j == length) { // watch for 000000000000000000
								computeValue = 0;
								break;
							}
						}
						while (j < length) {
							int digitValue = 0;
							if (radix == 8) {
								if ('0' <= source[j] && source[j] <= '7') {
									digitValue = source[j++] - '0';
								} else {
									throw new RuntimeException(
											"This is not a legal integer");
								}
							} else {
								if ('0' <= source[j] && source[j] <= '9') {
									digitValue = source[j++] - '0';
								} else if ('a' <= source[j] && source[j] <= 'f') {
									digitValue = source[j++] - 'a' + 10;
								} else if ('A' <= source[j] && source[j] <= 'F') {
									digitValue = source[j++] - 'A' + 10;
								}else if (source[j] == 'u' ||source[j] == 'l' || source[j] == 'U' || source[j] == 'L') {
									j++;
									continue;
								}  else {
									throw new RuntimeException(
											"This is not a legal integer");
								}
							}
							computeValue = (computeValue << shift) | digitValue;

						}
					}
				} else { // -----------regular case : radix = 10-----------
					for (int i = 0; i < length; i++) {
						int digitValue;
						if ('0' <= source[i] && source[i] <= '9') {
							digitValue = source[i] - '0';
						} else if (source[i] == 'u' ||source[i] == 'l' || source[i] == 'U' || source[i] == 'L') {
							continue;
						} else {
							throw new RuntimeException(
									"This is not a legal integer");
						}
						computeValue = 10 * computeValue + digitValue;
					}
				}
				intValue =computeValue;
				isInteger = true;
			} catch (RuntimeException e) {
			}
			
			if (isInteger) {
				expdata.value=new Expression(new IntegerFactor(intValue));
			} else {
				doubleValue = Double.valueOf(image);
				expdata.value=new Expression(new DoubleFactor(doubleValue));
			}
		}
		return data;
	}
	
	public Object visit(ASTConstantExpression node, Object data) {
		super.visit(node, data);
		return data;
	}
	
	public Object visit(ASTEqualityExpression node, Object data) {
		ExpressionVistorData expdata=(ExpressionVistorData)data;
		node.jjtGetChild(0).jjtAccept(this, expdata);
		Expression leftvalue=expdata.value;
		Expression rightvalue=null;
		try{
			//依次从左到右进行符号计算
			for (int i = 1; i < node.jjtGetNumChildren(); i++) {
				Node c = node.jjtGetChild(i);
				expdata.value = null;
				c.jjtAccept(this, expdata);
				rightvalue = expdata.value;
				if(leftvalue==null || rightvalue==null){
					throw new MyNullPointerException("EqualityExpression Value NULL in(.i) "+node.getBeginFileLine());
				}
				String operator = node.getOperatorType().get(i-1);
				if(leftvalue.isValueEqual(rightvalue,expdata.currentvex.getSymDomainset())){
					if (operator.equals("==")){
						leftvalue=new Expression(1);
					}else{
						leftvalue=new Expression(0);
					}
				}else if(leftvalue.isValueMustNotEqual(rightvalue,expdata.currentvex.getSymDomainset())){
					if (operator.equals("!=")){
						leftvalue=new Expression(1);
					}else{
						leftvalue=new Expression(0);
					}
				}else{
					//通过异常来处理此类情况
					throw new MyNullPointerException("EqualityExpression Value [0,1] in(.i) "+node.getBeginFileLine());
				}
			}
		}catch(MyNullPointerException e){
			super.visit(node,expdata);
			SymbolFactor sym=SymbolFactor.genSymbol(CType_BaseType.getBaseType("int"));
			expdata.currentvex.addSymbolDomain(sym, new IntegerDomain(0,1));
			leftvalue=new Expression(sym);
			expdata.value=leftvalue;
			return data;
		}
		expdata.value=leftvalue;
		return data;
	}
	
	public Object visit(ASTExclusiveORExpression node, Object data) {
		return dealBinaryBitOperation(node,data,"^");
	}
	
	public Object visit(ASTExpression node, Object data) {
		//zys:2010.8.11	在条件判断节点，如果超过了语法树深度上限，则不再递归访问其子结点
		int depth=node.getDescendantDepth();
		if(depth<=Config.MAXASTTREEDEPTH){
			super.visit(node, data);
		}else{
			//Logger.getRootLogger().info("ExpressionValueVisitor: ASTExpression in .i "+node.getBeginFileLine()+" depth="+depth+" overflow");
		}
		//super.visit(node, data);
		return data;
	}
	
	public Object visit(ASTFieldId node, Object data) {
		//在ASTPostfixExpression中统一处理
		return super.visit(node, data);
	}
	
	public Object visit(ASTInclusiveORExpression node, Object data) {
		return dealBinaryBitOperation(node,data,"|");
	}
	
	public Object visit(ASTLogicalANDExpression node, Object data) {
		ExpressionVistorData expdata=(ExpressionVistorData)data;
		node.jjtGetChild(0).jjtAccept(this, expdata);
		Expression leftvalue=expdata.value;
		Expression rightvalue=null;
		DoubleDomain d1=null;
		DoubleDomain d2=null;
		try{
			//从左到右进行符号计算
			for (int i = 1; i < node.jjtGetNumChildren(); i++) {
				Node c = node.jjtGetChild(i);
				expdata.value = null;
				c.jjtAccept(this, expdata);
				rightvalue = expdata.value;
				
				if(leftvalue==null || rightvalue==null){
					throw new MyNullPointerException("LogicalANDExpression Value NULL in(.i) "+node.getBeginFileLine());
				}
				//zys:2010.8.9	根据&&的短路特性，如果左表达式值为0,则不再计算右侧表达式的值
				d1=Domain.castToDoubleDomain(leftvalue.getDomain(expdata.currentvex.getSymDomainset()));
				if(d1!=null && d1.isCanonical() && d1.getMin()==0){
					leftvalue=new Expression(0);
					break;
				}
				
				d2=Domain.castToDoubleDomain(rightvalue.getDomain(expdata.currentvex.getSymDomainset()));
				if(d1!=null&&d2!=null){
					if(!d1.contains(0)&&!d2.contains(0)){
						leftvalue=new Expression(1);
						continue;
					}else if(d1.isCanonical()&&d1.getMin()==0){
						leftvalue=new Expression(0);
						continue;
					}else if(d2.isCanonical()&&d2.getMin()==0){
						leftvalue=new Expression(0);
						continue;
					}
				}else{
					throw new MyNullPointerException("LogicalANDExpression Domain NULL in(.i) "+node.getBeginFileLine());
				}
			}
		}catch(MyNullPointerException e){
			super.visit(node,expdata);
			SymbolFactor sym=SymbolFactor.genSymbol(CType_BaseType.getBaseType("int"));
			expdata.currentvex.addSymbolDomain(sym, new IntegerDomain(0,1));
			leftvalue=new Expression(sym);
			expdata.value=leftvalue;
			return data;
		}
			
		expdata.value=leftvalue;
		return data;
	}
	
	public Object visit(ASTLogicalORExpression node, Object data) {
		ExpressionVistorData expdata=(ExpressionVistorData)data;
		node.jjtGetChild(0).jjtAccept(this, expdata);
		
		Expression leftvalue=expdata.value;
		DoubleDomain d1=null;
		Expression rightvalue=null;
		DoubleDomain d2=null;
		try{
			//根据表达式的左值，依次从左到右进行符号计算，并根据表达式的符号进行计算
			for (int i = 1; i < node.jjtGetNumChildren(); i++) {
				Node c = node.jjtGetChild(i);
				expdata.value = null;
				c.jjtAccept(this, expdata);
				rightvalue = expdata.value;
				
				if(leftvalue==null || rightvalue==null){
					throw new MyNullPointerException("LogicalORExpression Value NULL in(.i) "+node.getBeginFileLine());
				}
				//zys:2010.8.9	根据||的短路特性，如果左表达式值为1,则不再计算右侧表达式的值
				d1=Domain.castToDoubleDomain(leftvalue.getDomain(expdata.currentvex.getSymDomainset()));
				if(d1!=null && !d1.contains(0)){
					leftvalue=new Expression(1);
					break;
				}
				
				d2=Domain.castToDoubleDomain(rightvalue.getDomain(expdata.currentvex.getSymDomainset()));
				if(d1!=null&&d2!=null){
					if(!d1.contains(0)||!d2.contains(0)){
						leftvalue=new Expression(1);
						break;
					}else if(d1.isCanonical()&&d1.getMin()==0&&d2.isCanonical()&&d2.getMin()==0){
						leftvalue=new Expression(0);
						continue;
					}
				}else{
					throw new MyNullPointerException("LogicalORExpression Domain NULL in(.i) "+node.getBeginFileLine());
				}
			}
		}catch(MyNullPointerException e){
			super.visit(node,expdata);
			SymbolFactor sym=SymbolFactor.genSymbol(CType_BaseType.getBaseType("int"));
			expdata.currentvex.addSymbolDomain(sym, new IntegerDomain(0,1));
			leftvalue=new Expression(sym);
			expdata.value=leftvalue;
			return data;
		}
		
		expdata.value=leftvalue;
		return data;
	}
	
	public Object visit(ASTMultiplicativeExpression node, Object data) {
		ExpressionVistorData expdata=(ExpressionVistorData)data;
		node.jjtGetChild(0).jjtAccept(this, expdata);
		Expression leftvalue=expdata.value;
		Expression rightvalue=null;
		try{	
			//从左到右进行符号计算
			for (int i = 1; i < node.jjtGetNumChildren(); i++) {
				Node c = node.jjtGetChild(i);
				expdata.value = null;
				c.jjtAccept(this, expdata);
				rightvalue = expdata.value;
				String operator = node.getOperatorType().get(i-1);
				if(leftvalue==null || rightvalue==null)
					throw new MyNullPointerException("MultiplicativeExpression Value NULL in(.i) "+node.getBeginFileLine());
				if (operator.equals("*")){
					//2010.12.03 liuli:当expression得长度过长时，会导致计算陷入死循环
					if(rightvalue.getTerms().size()*leftvalue.getTerms().size() >1000){
						IntegerDomain i1=Domain.castToIntegerDomain(leftvalue.getDomain(expdata.currentvex.getSymDomainset()));	
						IntegerDomain i2=Domain.castToIntegerDomain(rightvalue.getDomain(expdata.currentvex.getSymDomainset()));		
						if(i1!=null&&i2!=null&&i1.isCanonical()&&i2.isCanonical()){
							leftvalue=new Expression(i1.getMin()*i2.getMin());
						}else{
							leftvalue=new Expression(SymbolFactor.genSymbol(node.getType()));
						}
					}else{
						leftvalue=leftvalue.mul(rightvalue);
					}	
				}else if (operator.equals("/")){
					if(rightvalue.getTerms().size()*leftvalue.getTerms().size() >1000){
						IntegerDomain i1=Domain.castToIntegerDomain(leftvalue.getDomain(expdata.currentvex.getSymDomainset()));	
						IntegerDomain i2=Domain.castToIntegerDomain(rightvalue.getDomain(expdata.currentvex.getSymDomainset()));		
						if(i1!=null&&i2!=null&&i1.isCanonical()&&i2.isCanonical()){
							if(i2.getMin()==0)
							{
								leftvalue=new Expression(IntegerDomain.DEFAULT_MAX);
							}else
							{
								leftvalue=new Expression(i1.getMin()/i2.getMin());
							}
						}else{
							leftvalue=new Expression(SymbolFactor.genSymbol(node.getType()));
						}
					}else{
						leftvalue=leftvalue.div(rightvalue);
					}					
				}else{//%
					IntegerDomain i1=Domain.castToIntegerDomain(leftvalue.getDomain(expdata.currentvex.getSymDomainset()));	
					IntegerDomain i2=Domain.castToIntegerDomain(rightvalue.getDomain(expdata.currentvex.getSymDomainset()));		
					if(i1!=null&&i2!=null&&i1.isCanonical()&&i2.isCanonical()){
						if(i2.getMin()==0)
						{
							leftvalue=new Expression(IntegerDomain.DEFAULT_MAX);
						}else
						{
							leftvalue=new Expression(i1.getMin()%i2.getMin());
						}
					}else{
						leftvalue=new Expression(SymbolFactor.genSymbol(CType_BaseType.getBaseType("int")));
						continue;
					}
				}
			}
		}catch(MyNullPointerException e){
			super.visit(node,expdata);
			SymbolFactor sym=SymbolFactor.genSymbol(CType_BaseType.getBaseType("double"));
			if(Config.USEUNKNOWN)
				expdata.currentvex.addSymbolDomain(sym, DoubleDomain.getUnknownDomain());
			else
				expdata.currentvex.addSymbolDomain(sym, DoubleDomain.getFullDomain());
			leftvalue=new Expression(sym);
			expdata.value=leftvalue;
			return data;
		}
		expdata.value=leftvalue;
		return data;
	}
	
	public Object visit(ASTPostfixExpression node, Object data) {
		ExpressionVistorData expdata=(ExpressionVistorData)data;
		ASTPrimaryExpression primary=(ASTPrimaryExpression)node.jjtGetChild(0);
		primary.jjtAccept(this, data);
		ArrayList<Boolean> flags=node.getFlags();
		ArrayList<String> operators=node.getOperatorType();
		Expression currentvalue=expdata.value;		
		CType currenttype=primary.getType();
		int j=1;
		for(int i=0;i<flags.size();i++){
			boolean flag=flags.get(i);
			String operator=operators.get(i);
			if(operator.equals("[")){
				ASTExpression expression =null;
				if(flag){
					expression=(ASTExpression)node.jjtGetChild(j++);
					expression.jjtAccept(this, data);					
					if(Config.Field){
						//for循环的目的是 循环体出现异常时及时终止循环体执行并跳出
						for(int loopFlag=0;loopFlag<1;loopFlag++)
						{
							try
							{
								ExpressionVistorData expdataIndex=(ExpressionVistorData)data;
								Domain domain=expdataIndex.value.getDomain(expdataIndex.currentvex.getSymDomainset());
								IntegerDomain vDomain=Domain.castToIntegerDomain(domain);
												
								if(vDomain!=null)
								{
									VariableNameDeclaration array = null;							
									NameDeclaration declArr=Search.searchInVariableAndMethodUpward(primary.getImage(), node.getScope());
									if (declArr instanceof VariableNameDeclaration) {
										array = (VariableNameDeclaration) declArr;								
									}
									if(array.getType() instanceof CType_Array)
									{										
										CType_Array temp = (CType_Array) array.getType();
										long length=temp.getDimSize();
										IntegerDomain arrDomain=new IntegerDomain(new IntegerInterval(0,length));							
										vDomain=IntegerDomain.intersect(arrDomain, vDomain);
																			
										List<Integer> intNums=vDomain.getNums();
										for(int intN=0;intN<intNums.size();intN++)
										{
											int index=intNums.get(intN).intValue();							
											String arrImage=primary.getImage()+"["+index+"]";
											NameDeclaration declArrar=Search.searchInVariableAndMethodUpward(arrImage, node.getScope());								
											if(declArrar!=null&&expdata!=null)
											{ 
												expdata.arrayIndex.add(new Integer(index));
												
											}else
											{
												break;
											}
											
										}
									}else if(array.getType() instanceof CType_Pointer)
									{										
										CType_Pointer temp = (CType_Pointer) array.getType();
										long length=Config.MaxArray;
										IntegerDomain arrDomain=new IntegerDomain(new IntegerInterval(0,length));							
										vDomain=IntegerDomain.intersect(arrDomain, vDomain);
																			
										List<Integer> intNums=vDomain.getNums();
										for(int intN=0;intN<intNums.size();intN++)
										{
											int index=intNums.get(intN).intValue();							
											String arrImage=primary.getImage()+"["+index+"]";
											NameDeclaration declArrar=Search.searchInVariableAndMethodUpward(arrImage, node.getScope());								
											if(declArrar!=null&&expdata!=null)
											{ 
												expdata.arrayIndex.add(new Integer(index));
												
											}else
											{
												break;
											}
											
										}
									}
								}
							}catch(Exception e)
							{
								break;
							}
						}
																		
						Scope scope=node.getScope();
			        	NameDeclaration decl=Search.searchInVariableAndMethodUpward(node.getImage(), scope);
			        	if(decl instanceof VariableNameDeclaration){
			        		//变量处理 
			        		VariableNameDeclaration v=(VariableNameDeclaration)decl;
			        		currentvalue=expdata.currentvex.getValue(v);
			        	}
					}
				}else{
					throw new RuntimeException("ASTPostfixExpression error!");
				}
				//zys:2010.9.13 华为测试出错，暂时屏蔽下
				if(currenttype==null){
					Scope scope=node.getScope();
					NameDeclaration decl0=Search.searchInVariableAndMethodUpward(primary.getImage(), scope);
					if(decl0!=null&&decl0 instanceof VariableNameDeclaration)
					{
						VariableNameDeclaration decl00=(VariableNameDeclaration)decl0;
						currenttype=decl00.getType();
					}
					if(currenttype==null)
					{
						logger.error(primary.getBeginFileLine()+"行的类型分析错误");
						throw new RuntimeException(primary.getBeginFileLine()+"行的类型分析错误");
					}
				}
				CType atype=currenttype.getSimpleType();
				if(atype instanceof CType_AbstPointer){
					CType_AbstPointer ptype=(CType_AbstPointer) atype;
					currenttype=ptype.getOriginaltype();
					if(currentvalue!=null){
					Domain domain=Domain.castToType(currentvalue.getDomain(expdata.currentvex.getSymDomainset()), atype);
					if(domain instanceof PointerDomain){
						PointerDomain pdomain=(PointerDomain)domain;
						SymbolFactor sym=SymbolFactor.genSymbol(atype);
						if(currenttype.getSimpleType() instanceof CType_Array){
							CType_Array temp=(CType_Array)currenttype.getSimpleType();
							if(temp.isFixed()){
								pdomain =new PointerDomain();
								pdomain.setElementtype(currenttype);
								pdomain.setLength(new Expression(temp.getDimSize()));
								expdata.currentvex.addSymbolDomain(sym, pdomain);;
								}
							}
							currentvalue=new Expression(sym);
						}
					}
				}
			}else if(operator.equals("(")){
				ASTArgumentExpressionList expressionlist=null;
				//add by zhouhb
				//对指针相关函数的处理
				//增减了模糊处理
				//add by zhouhb 2010/10/19
				//if(node.getImage().contains("malloc")||node.getImage().contains("Malloc")||node.getImage().contains("malloc"))
				if(node.getImage().equals("malloc"))
				{
					//增加了对malloc参数中包含函数参数引用的判断，对传入的未知参数不予处理
					//add by zhouhb 2010/8/18
					if(((SimpleNode)node.jjtGetChild(1)).containsChildOfType(ASTPrimaryExpression.class)){
						List<Node> primarys =((SimpleNode)node.jjtGetChild(1)).findChildrenOfType(ASTPrimaryExpression.class);
           				for(Node pri:primarys)
           				{
           					if(pri.jjtGetNumChildren()==0){
           						VariableNameDeclaration v =((SimpleNode)pri).getVariableNameDeclaration();
           						if(v!=null&&v.getScope() instanceof SourceFileScope)
           							return data;
           					}
           				}
					}
						node.jjtGetChild(1).jjtAccept(this, expdata);
						if(node.containsChildOfType(ASTTypeName.class)){
							ASTTypeName type=(ASTTypeName)node.getFirstChildOfType(ASTTypeName.class);
							expdata.value=expdata.value.div(new Expression(type.getType().getSize()));
						}
						//处理malloc(10)时无类型信息，故修改
						//modified by zhouhb 2010/7/19
						long mallocsize;
						if(expdata.value==null)
						{
							return data;
						}
						IntegerDomain size=IntegerDomain.castToIntegerDomain(expdata.value.getDomain(expdata.currentvex.getSymDomainset()));
						//如果malloc分配空间以参数传递进来，默认分配无穷大
						if(size!=null&&!size.isEmpty()&&!size.getIntervals().isEmpty()){
							mallocsize=(int)size.getIntervals().first().getMin();
						}else{
							mallocsize=IntegerDomain.DEFAULT_MAX;
						}
						SymbolFactor sym=SymbolFactor.genSymbol(node.getType());
						PointerDomain p=new PointerDomain();
						p.offsetRange=new IntegerDomain(0,mallocsize-1);
						//p.AllocType=CType_AllocType.heapType;
						if(p.Type.contains(CType_AllocType.NotNull)){
							p.Type.remove(CType_AllocType.NotNull);
						}
						p.Type.add(CType_AllocType.heapType);
						p.setValue(PointerValue.NULL_OR_NOTNULL);
						expdata.currentvex.addSymbolDomain(sym, p);
						expdata.value=new Expression(sym);
						return data;
//				}else if(node.getImage().equals("calloc")){
//					if(((SimpleNode)node.jjtGetChild(1)).containsChildOfType(ASTPrimaryExpression.class)){
//						List<Node> primarys =((SimpleNode)node.jjtGetChild(1)).findChildrenOfType(ASTPrimaryExpression.class);
//           				for(Node pri:primarys)
//           				{
//           					if(pri.jjtGetNumChildren()==0){
//           						VariableNameDeclaration v =((SimpleNode)pri).getVariableNameDeclaration();
//           						if(v!=null&&v.getScope() instanceof SourceFileScope)
//           							return data;
//           					}
//           				}
//					}
//						node.jjtGetChild(1).jjtAccept(this, expdata);
//						if(node.containsChildOfType(ASTTypeName.class)){
//						ASTTypeName type=(ASTTypeName)node.getFirstChildOfType(ASTTypeName.class);
//						if(type.getType()!=null){
//							long callocsize;
//							IntegerDomain size=IntegerDomain.castToIntegerDomain(expdata.value.getDomain(expdata.currentvex.getSymDomainset()));
//							if(size==null){
//								callocsize=IntegerDomain.DEFAULT_MAX;
//							}else{
//								callocsize=(int)size.getIntervals().first().getMin();
//							}
//							SymbolFactor sym=SymbolFactor.genSymbol(node.getType());
//							PointerDomain p=new PointerDomain();
//							p.offsetRange=new IntegerDomain(0,callocsize-1);
//							//p.AllocType=CType_AllocType.heapType;
//							if(p.Type.contains(CType_AllocType.NotNull)){
//								p.Type.remove(CType_AllocType.NotNull);
//							}
//							p.Type.add(CType_AllocType.heapType);
//							p.setValue(PointerValue.NULL_OR_NOTNULL);
//							expdata.currentvex.addSymbolDomain(sym, p);
//							expdata.value=new Expression(sym);
//							return data;
//							}
//						}
//				}if(node.getImage().equals("xmalloc")){
//					node.jjtGetChild(1).jjtAccept(this, expdata);
//					node.setType(CType_Pointer.VOID);
//					SymbolFactor sym=SymbolFactor.genSymbol(node.getType());
//					PointerDomain p=new PointerDomain();
//					//p.AllocType=CType_AllocType.heapType;
//					if(p.Type.contains(CType_AllocType.NotNull)){
//						p.Type.remove(CType_AllocType.NotNull);
//					}
//					p.Type.add(CType_AllocType.heapType);
//					p.setValue(PointerValue.NOTNULL);
//					expdata.currentvex.addSymbolDomain(sym, p);
//					expdata.value=new Expression(sym);
//					return data;
//				}else if(node.getImage().equals("realloc")){
//					if(((SimpleNode)node.jjtGetChild(1)).containsChildOfType(ASTPrimaryExpression.class)){
//						List<Node> primarys =((SimpleNode)node.jjtGetChild(1)).findChildrenOfType(ASTPrimaryExpression.class);
//           				for(Node pri:primarys)
//           				{
//           					if(pri.jjtGetNumChildren()==0){
//           						VariableNameDeclaration v =((SimpleNode)pri).getVariableNameDeclaration();
//           						if(v!=null&&v.getScope() instanceof SourceFileScope)
//           							return data;
//           					}
//           				}
//					}
//							node.jjtGetChild(1).jjtAccept(this, expdata);
//							long reallocsize;
//							IntegerDomain size=IntegerDomain.castToIntegerDomain(expdata.value.getDomain(expdata.currentvex.getSymDomainset()));
//							if(size==null){
//								reallocsize=IntegerDomain.DEFAULT_MAX;
//							}else{
//								reallocsize=(int)size.getIntervals().first().getMin();
//							}
//							SymbolFactor sym=SymbolFactor.genSymbol(node.getType());
//							PointerDomain p=new PointerDomain();
//							p.offsetRange=new IntegerDomain(0,reallocsize-1);
//							//p.AllocType=CType_AllocType.heapType;
//							if(p.Type.contains(CType_AllocType.NotNull)){
//								p.Type.remove(CType_AllocType.NotNull);
//							}
//							p.Type.add(CType_AllocType.heapType);
//							p.setValue(PointerValue.NULL_OR_NOTNULL);
//							//同步符号对应的区间值
//							ASTPrimaryExpression pri = (ASTPrimaryExpression)((SimpleNode)node.jjtGetChild(1)).getFirstChildOfType(ASTPrimaryExpression.class);
//							VariableNameDeclaration v = pri.getVariableDecl();
//							Expression ve=expdata.currentvex.getValue(v);
//							SymbolFactor temp=(SymbolFactor)ve.getSingleFactor();
//							expdata.currentvex.addSymbolDomain(temp, p);
//							expdata.currentvex.addSymbolDomain(sym, p);
//							expdata.value=new Expression(sym);
//							return data;
				}//增减了模糊处理
				//add by zhouhb 2010/10/19
//				else if(node.getImage().contains("free")||node.getImage().contains("Free")||node.getImage().contains("FREE")){
				else if(node.getImage().equals("free")){		
						node.jjtGetChild(1).jjtAccept(this, expdata);
						PointerDomain p=new PointerDomain();
						p.offsetRange=new IntegerDomain(0,0);
						//p.AllocType=CType_AllocType.Null;
						p.Type.add(CType_AllocType.Null);
						p.setValue(PointerValue.NULL);
						VariableNameDeclaration v;
						if(!Config.Field){
							ASTPrimaryExpression pri = (ASTPrimaryExpression)((SimpleNode)node.jjtGetChild(1)).getFirstChildOfType(ASTPrimaryExpression.class);
							v = pri.getVariableDecl();
							//结构体成员的free不予以处理
							//add by zhouhb 2010/8/18
								if(v!=null&&(v.getType()instanceof CType_Pointer&&CType_Pointer.getOrignType(v.getType()) instanceof CType_Struct)){
									return data;
								}
						}else{
							ASTPostfixExpression po = (ASTPostfixExpression)((SimpleNode)node.jjtGetChild(1)).getFirstChildOfType(ASTPostfixExpression.class);
							v = (VariableNameDeclaration)Search.searchInVariableAndMethodUpward(po.getImage(), node.getScope());
						}
						Expression ve=null;
						if(v!=null)
							ve=expdata.currentvex.getValue(v);
						if(ve==null || ve!=null && !(ve.getSingleFactor() instanceof SymbolFactor))
							return data;
						SymbolFactor temp=(SymbolFactor)ve.getSingleFactor();
						//如果释放对象指针有运算，即ve不为SingleFactor(eg.1+S)，则释放不成功
						if(temp==null){
							return data;
						}else{
						expdata.currentvex.addSymbolDomain(temp, p);
						expdata.value=new Expression(temp);
						return data;
						}
				}
//				}//用于处理字符串的标准库函数的相应指针运算操作
				//处理串拷贝时处理了左操作数为变量，右操作数为常量或变量的情况
				//2010/7/19
				//增加了左变量为表达式情况的处理
				else if(node.getImage().equals("strcpy")){
					node.jjtGetChild(1).jjtAccept(this, expdata);		
					ASTPrimaryExpression priLeft = (ASTPrimaryExpression)((SimpleNode)node.jjtGetChild(1)).getFirstChildOfType(ASTPrimaryExpression.class);
					VariableNameDeclaration vLeft = priLeft.getVariableDecl();
					if(vLeft!=null){
						Expression eLeft=expdata.currentvex.getValue(vLeft);
						if(eLeft!=null){
							Domain vDomainTemp=eLeft.getDomain(expdata.currentvex.getSymDomainset());
							if(vLeft.getType() instanceof CType_Pointer){
								PointerDomain vDomain=(PointerDomain)Domain.castToType(vDomainTemp,vLeft.getType());
								try{
									if(eLeft.getSingleFactor() instanceof SymbolFactor&&vDomain!=null){
										Domain tempDomain=vDomain.clone();
										//右操作数为常量时的处理	
										if(node.containsChildOfType(ASTConstant.class)){
											ASTConstant con = (ASTConstant)((SimpleNode)node.jjtGetChild(1)).getFirstChildOfType(ASTConstant.class);
											if(!(eLeft.getSingleFactor() instanceof SymbolFactor))
												return data;
											SymbolFactor temp=(SymbolFactor)eLeft.getSingleFactor();
											((PointerDomain)tempDomain).allocRange=new IntegerDomain(con.getImage().length()-1,con.getImage().length()-1);
											expdata.currentvex.addSymbolDomain(temp, tempDomain);
										}//右操作数为变量或函数调用时的处理	
										else{
											ASTPrimaryExpression priRight = (ASTPrimaryExpression)((SimpleNode)node.jjtGetChild(1).jjtGetChild(1)).getFirstChildOfType(ASTPrimaryExpression.class);
											//右操作数为变量
											if(!priRight.isMethod()){
												VariableNameDeclaration vRight = priRight.getVariableDecl();
												//处理不了的类型默认区间未知
												if(vRight==null)
												{
													return data;
												}
										
												Expression eRight=expdata.currentvex.getValue(vRight);
												//处理不了的类型默认区间未知
												if(eRight==null){
													return data;
												}
												PointerDomain size=(PointerDomain)Domain.castToType(eRight.getDomain(expdata.currentvex.getSymDomainset()),vRight.getType());
												//右操作数为参数传递时size为空
												if(size==null){
													size=new PointerDomain();
													size.allocRange=new IntegerDomain(0,IntegerDomain.DEFAULT_MAX);
												}else{
													((PointerDomain)tempDomain).allocRange=size.allocRange;
												}
												SymbolFactor temp=(SymbolFactor)eLeft.getSingleFactor();
												expdata.currentvex.addSymbolDomain(temp, tempDomain);
											}//右操作数为函数调用
											else{
												
											}
										}
									}
								}catch(CloneNotSupportedException e){
									e.printStackTrace();
									return null;
								}
							}
						}
					}
					return data;
				}
				else if(node.getImage().equals("sqrt")){
					expressionlist=(ASTArgumentExpressionList)node.jjtGetChild(1);
					if(expressionlist!=null)
					{
						expressionlist.jjtGetChild(0).jjtAccept(this, expdata);
						DoubleDomain ddomain=DoubleDomain.castToDoubleDomain(expdata.value.getDomain(expdata.currentvex.getSymDomainset()));
						
						if(ddomain instanceof DoubleDomain&& !ddomain.isUnknown())
						{
							ddomain=DoubleDomain.sqrt(ddomain);							
							SymbolFactor sym=SymbolFactor.genSymbol(node.getType());
							expdata.currentvex.addSymbolDomain(sym, ddomain);
							expdata.value=new Expression(sym);
						}
					}				
					return data;
				}else if(node.getImage().equals("strncpy")){
					node.jjtGetChild(1).jjtAccept(this, expdata);		
					ASTPrimaryExpression priLeft = (ASTPrimaryExpression)((SimpleNode)node.jjtGetChild(1)).getFirstChildOfType(ASTPrimaryExpression.class);
					VariableNameDeclaration vLeft = priLeft.getVariableDecl();
					if(vLeft!=null){
						Expression eLeft=expdata.currentvex.getValue(vLeft);
						if(eLeft!=null){
							Domain vDomainTemp=eLeft.getDomain(expdata.currentvex.getSymDomainset());
							if(vLeft.getType() instanceof CType_Pointer){
								PointerDomain vDomain=(PointerDomain)Domain.castToType(vDomainTemp,vLeft.getType());
								try{
									if(eLeft.getSingleFactor() instanceof SymbolFactor&&vDomain!=null){
										Domain tempDomain=vDomain.clone();
										//右操作数为常量时的处理	
										if(node.containsChildOfType(ASTConstant.class)){
											ASTConstant con = (ASTConstant)((SimpleNode)node.jjtGetChild(1)).getFirstChildOfType(ASTConstant.class);
											if(!(eLeft.getSingleFactor() instanceof SymbolFactor))
												return data;
											SymbolFactor temp=(SymbolFactor)eLeft.getSingleFactor();
											((PointerDomain)tempDomain).allocRange=new IntegerDomain(con.getImage().length()-1,con.getImage().length()-1);
											expdata.currentvex.addSymbolDomain(temp, tempDomain);
										}//右操作数为变量或函数调用时的处理	
										else{
											ASTPrimaryExpression priRight = (ASTPrimaryExpression)((SimpleNode)node.jjtGetChild(1).jjtGetChild(1)).getFirstChildOfType(ASTPrimaryExpression.class);
											//右操作数为变量
											if(!priRight.isMethod()){
												VariableNameDeclaration vRight = priRight.getVariableDecl();
												//处理不了的类型默认区间未知
												if(vRight==null)
												{
													return data;
												}
										
												Expression eRight=expdata.currentvex.getValue(vRight);
												//处理不了的类型默认区间未知
												if(eRight==null){
													return data;
												}
																								
												PointerDomain size=(PointerDomain)Domain.castToPointerDomain(eRight.getDomain(expdata.currentvex.getSymDomainset()));
												//右操作数为参数传递时size为空
												if(size==null){
													size=new PointerDomain();
													size.allocRange=new IntegerDomain(0,IntegerDomain.DEFAULT_MAX);
												}else{
													((PointerDomain)tempDomain).allocRange=size.allocRange;
												}
												SymbolFactor temp=(SymbolFactor)eLeft.getSingleFactor();
												expdata.currentvex.addSymbolDomain(temp, tempDomain);
											}//右操作数为函数调用
											else{
												
											}
										}
									}
								}catch(CloneNotSupportedException e){
									e.printStackTrace();
									return null;
								}
							}else if(vLeft.getType() instanceof CType_Array){
								PointerDomain vDomain=(PointerDomain)Domain.castToType(vDomainTemp,vLeft.getType());
								try{
									if(eLeft.getSingleFactor() instanceof SymbolFactor&&vDomain!=null){
										Domain tempDomain=vDomain.clone();
										//右操作数为常量时的处理	
										SimpleNode argNode=(SimpleNode)node.jjtGetChild(1);
										if(((SimpleNode)argNode.jjtGetChild(1)).containsChildOfType(ASTConstant.class)){
											ASTConstant con = (ASTConstant)((SimpleNode)argNode.jjtGetChild(1)).getFirstChildOfType(ASTConstant.class);
											if(!(eLeft.getSingleFactor() instanceof SymbolFactor))
												return data;
											SymbolFactor temp=(SymbolFactor)eLeft.getSingleFactor();
											((PointerDomain)tempDomain).allocRange=new IntegerDomain(con.getImage().length()-1,con.getImage().length()-1);
											expdata.currentvex.addSymbolDomain(temp, tempDomain);
										}//右操作数为变量或函数调用时的处理	
										else{
											ASTPrimaryExpression priRight = (ASTPrimaryExpression)((SimpleNode)node.jjtGetChild(1).jjtGetChild(1)).getFirstChildOfType(ASTPrimaryExpression.class);
											//右操作数为变量
											if(!priRight.isMethod()){
												VariableNameDeclaration vRight = priRight.getVariableDecl();
												//处理不了的类型默认区间未知
												if(vRight==null)
												{
													return data;
												}
										
												Expression eRight=expdata.currentvex.getValue(vRight);
												//处理不了的类型默认区间未知
												if(eRight==null){
													return data;
												}
												
												PointerDomain size=(PointerDomain)Domain.castToType(eRight.getDomain(expdata.currentvex.getSymDomainset()),vRight.getType());
												//右操作数为参数传递时size为空
												if(size==null){
													size=new PointerDomain();
													size.allocRange=new IntegerDomain(0,IntegerDomain.DEFAULT_MAX);
												}else{
													((PointerDomain)tempDomain).allocRange=size.allocRange;
												}
												SymbolFactor temp=(SymbolFactor)eLeft.getSingleFactor();
												expdata.currentvex.addSymbolDomain(temp, tempDomain);
											}//右操作数为函数调用
											else{
												
											}
										}
										node.jjtGetChild(1).jjtGetChild(2).jjtAccept(this, expdata);
										Expression thirdValue=expdata.value;
										IntegerDomain thirdDomain=(IntegerDomain)Domain.castToIntegerDomain(thirdValue.getDomain(expdata.currentvex.getLastsymboldomainset()));
										thirdDomain=(IntegerDomain) Domain.intersect(thirdDomain, new IntegerDomain(0,IntegerDomain.DEFAULT_MAX), new CType_BaseType("int"));
										((PointerDomain)tempDomain).allocRange=(IntegerDomain) Domain.union(((PointerDomain)tempDomain).allocRange,thirdDomain,new CType_BaseType("int"));
									}
								}catch(CloneNotSupportedException e){
									e.printStackTrace();
									return null;
								}
							}
						}
					}
					return data;
				}
				//处理串连接时处理了左操作数为变量，右操作数为常量或变量的情况
//				else if(node.getImage().equals("strcat")){
//					node.jjtGetChild(1).jjtAccept(this, expdata);	
//					ASTPrimaryExpression priLeft = (ASTPrimaryExpression)((SimpleNode)node.jjtGetChild(1)).getFirstChildOfType(ASTPrimaryExpression.class);
//					VariableNameDeclaration vLeft = priLeft.getVariableDecl();
//					if(vLeft!=null)
//					{
//						Expression eLeft=expdata.currentvex.getValue(vLeft);
//						Domain vDomain=eLeft.getDomain(expdata.currentvex.getSymDomainset());
//						try{
//							if(eLeft.getSingleFactor() instanceof SymbolFactor&&vDomain!=null){
//								//右操作数为常量时的处理	
//								Domain tempDomain=vDomain.clone();
//								if(node.containsChildOfType(ASTConstant.class)){
//								ASTConstant con = (ASTConstant)((SimpleNode)node.jjtGetChild(1)).getFirstChildOfType(ASTConstant.class);
//								SymbolFactor temp=(SymbolFactor)eLeft.getSingleFactor();
//								((PointerDomain)tempDomain).allocRange=IntegerDomain.add(((PointerDomain)vDomain).allocRange,con.getImage().length()-2);
//								expdata.currentvex.addSymbolDomain(temp, tempDomain);
//							}//右操作数为变量时的处理	
//							else{ASTPrimaryExpression priRight = (ASTPrimaryExpression)((SimpleNode)node.jjtGetChild(1).jjtGetChild(1)).getFirstChildOfType(ASTPrimaryExpression.class);
//								VariableNameDeclaration vRight = priRight.getVariableDecl();
//								Expression eRight=expdata.currentvex.getValue(vRight);
//								PointerDomain size=(PointerDomain)eRight.getDomain(expdata.currentvex.getSymDomainset());
//								//右操作数为参数传递时size为空
//								if(size==null){
//									size=new PointerDomain();
//									size.allocRange=new IntegerDomain(0,IntegerDomain.DEFAULT_MAX);
//								}else{
//									((PointerDomain)tempDomain).allocRange=IntegerDomain.add(((PointerDomain)tempDomain).allocRange,IntegerDomain.sub(size.allocRange,1));
//								}
//								SymbolFactor temp=(SymbolFactor)eLeft.getSingleFactor();
//								expdata.currentvex.addSymbolDomain(temp, tempDomain);
//								}
//							}
//						}catch(CloneNotSupportedException e){
//							e.printStackTrace();
//							return null;
//						}
//					}
//					return data;
//				}else if(node.getImage().equals("strncpy")){
//					//待处理
//				}else if(node.getImage().equals("strncat")){
//					//待处理
//				}//处理的很不准确，为了减少误报，暂且屏蔽
				 //modified by zhouhb 2010/8/18
//				else if(node.getImage().equals("strlen")){
//					Object re = ((SimpleNode)node.jjtGetChild(1)).getVariableNameDeclaration();
//					if(expdata.value==null){
//						SymbolFactor s=SymbolFactor.genSymbol(node.getType());
//    					expdata.value=new Expression(s);
//					}
//					SymbolFactor sym=(SymbolFactor)expdata.value.getSingleFactor();
//					if(re instanceof VariableNameDeclaration){
//						Expression e=expdata.currentvex.getValue((VariableNameDeclaration)re);
//						//对若通过参数传递，则进行判断
//						//add by zhouhb 2010/7/19
//						if(e==null){
//							IntegerDomain size=new IntegerDomain(IntegerDomain.DEFAULT_MIN,IntegerDomain.DEFAULT_MAX);
//							expdata.currentvex.addSymbolDomain(sym, size);
//						}else{
//						Domain vDomain=e.getDomain(expdata.currentvex.getSymDomainset());
//						if(vDomain instanceof PointerDomain){
//						    IntegerDomain size=IntegerDomain.sub(((PointerDomain)vDomain).allocRange,1);
//						    if(size.getIntervals().contains(new IntegerInterval(-1,-1))){
//								size.intervals.remove(new IntegerInterval(-1,-1));
//								size.intervals.add(new IntegerInterval(0,0));
//						    }
//							expdata.currentvex.addSymbolDomain(sym, size);
//						    }
//						}
//					}else if(node.containsChildOfType(ASTConstant.class)){
//						ASTConstant con = (ASTConstant)node.getFirstChildOfType(ASTConstant.class);
//						IntegerDomain size=new IntegerDomain(con.getImage().length()-2,con.getImage().length()-2);
//						expdata.currentvex.addSymbolDomain(sym,size);
//					}
//					
//				}
				if(flag){
					expressionlist=(ASTArgumentExpressionList)node.jjtGetChild(j++);
					expressionlist.jjtAccept(this, data);
				}
			}else if(operator.equals(".")){
				ASTFieldId field=null;
				if(flag){
					field=(ASTFieldId)node.jjtGetChild(j++);
					field.jjtAccept(this, data);
					if(Config.Field){
						Scope scope=node.getScope();
			        	NameDeclaration decl=Search.searchInVariableAndMethodUpward(node.getImage(), scope);
			        	if(decl instanceof VariableNameDeclaration){
			        		//变量处理
			        		VariableNameDeclaration v=(VariableNameDeclaration)decl;
			        		currentvalue=expdata.currentvex.getValue(v);
			        		if(currentvalue==null){
			        			SymbolFactor sym=SymbolFactor.genSymbol(v.getType(),v.getImage());
								expdata.value=new Expression(sym);
								expdata.currentvex.addValue(v, expdata.value);
			        		}
			        		}
					}
				}else{
					throw new RuntimeException("ASTPostfixExpression error!");
				}
				if(Config.Field){
					if(currentvalue==null){
						currentvalue=new Expression(SymbolFactor.genSymbol(field.getType()));
					}
				}else
					currentvalue=new Expression(SymbolFactor.genSymbol(field.getType()));
			}else if(operator.equals("->")){
				ASTFieldId field=null;
				if(flag){
					field=(ASTFieldId)node.jjtGetChild(j++);
					field.jjtAccept(this, data);
					if(Config.Field){
						Scope scope=node.getScope();
			        	NameDeclaration decl=Search.searchInVariableAndMethodUpward(node.getImage(), scope);
			        	if(decl instanceof VariableNameDeclaration){
			        		//变量处理
			        		VariableNameDeclaration v=(VariableNameDeclaration)decl;
			        		currentvalue=expdata.currentvex.getValue(v);
			        		}
					}
				}else{
					throw new RuntimeException("ASTPostfixExpression error!");
				}
				if(Config.Field){
					if(currentvalue==null){
						currentvalue=new Expression(SymbolFactor.genSymbol(field.getType()));
					}
				}else
					currentvalue=new Expression(SymbolFactor.genSymbol(field.getType()));
			}else if(operator.equals("++")&&currentvalue!=null){
				Expression temp=currentvalue.add(new Expression(1));
				ASTPrimaryExpression p = (ASTPrimaryExpression) ((SimpleNode)node.jjtGetChild(j-1)).getSingleChildofType(ASTPrimaryExpression.class);
				if(p!=null){
					VariableNameDeclaration v = p.getVariableDecl();
					if (v != null && expdata.sideeffect && expdata.currentvex != null) {
						expdata.currentvex.addValue(v, temp);
						
					}
				}
				if(Config.Field){
					VariableNameDeclaration v = node.getVariableDecl();
					if (v != null && expdata.sideeffect && expdata.currentvex != null&&expdata.value!=null) {
						expdata.currentvex.addValue(v, temp);
					}
				}
			}else if(operator.equals("--")&&currentvalue!=null){
				Expression temp=currentvalue.sub(new Expression(1));
				ASTPrimaryExpression p = (ASTPrimaryExpression) ((SimpleNode)node.jjtGetChild(j-1)).getSingleChildofType(ASTPrimaryExpression.class);
				if(p!=null){
					VariableNameDeclaration v = p.getVariableDecl();
					if (v != null && expdata.sideeffect && expdata.currentvex != null) {
						expdata.currentvex.addValue(v, temp);
					}
				}
				if(Config.Field){
					VariableNameDeclaration v = node.getVariableDecl();
					if (v != null && expdata.sideeffect && expdata.currentvex != null&&expdata.value!=null) {
						expdata.currentvex.addValue(v, temp);
					}
				}
			}else{
				currentvalue=new Expression(SymbolFactor.genSymbol(CType_BaseType.getBaseType("int")));
			}
		}
		//add by zhouhb
		//处理p=f(a,b)时，会为f,a,b分别生成三个符号F,A,B，最终会生成一个新的符号P，但并未把F对应的区间与P关联
		//忘了当时为什么这么改，暂且保留
//		if(primary.jjtGetNumChildren()==0&&primary.getType() instanceof CType_Function){
//			currentvalue=func;
//		}
		expdata.value=currentvalue;
		return data;
	}
	
	
    @Override
	public Object visit(ASTPrimaryExpression node, Object data) {
    	super.visit(node, data);
    	ExpressionVistorData expdata=(ExpressionVistorData)data;
    	String image=node.getImage();
    	if(!image.equals("")){
    		if(image.equals("NULL"))
    		{
    			SymbolFactor sf =SymbolFactor.genSymbol(new CType_Pointer());
    			expdata.currentvex.addSymbolDomain(sf,PointerDomain.getNullDomain());
    			expdata.value = new Expression(sf);
    			return expdata;
    		}
    		
    		//处理出现
    		Scope scope=node.getScope();
        	NameDeclaration decl=Search.searchInVariableAndMethodUpward(image, scope);
        	if(decl instanceof VariableNameDeclaration){
        		//变量处理
        		VariableNameDeclaration v=(VariableNameDeclaration)decl;
        		expdata.value=expdata.currentvex.getValue(v);
        		//不处理结构体的相关信息
        		//add by zhouhb 2010/8/19
        		if(!Config.Field){
        			if(v.getType() instanceof CType_Array && ((CType_Array)v.getType()).getOriginaltype() instanceof CType_Struct||v.getType() instanceof CType_Struct)
            			return data;
        		}
        		if(expdata.value==null){
        			//全局变量初值处理 如果有全局变量，且初始值在声明时给出，则加入到当前结点中 ssj
        			//全局变量不能初始化，例如main调用a()和b(),a()修改了global，b()在分析时就不能
        			//取global的初始值了
//        			if(v.getScope() instanceof SourceFileScope){
//        				Variable var = v.getVariable();
//        				if(var == null){
//        					if(var.getValue() instanceof Double){
//            					double vardouble = new Double(var.getValue().toString());
//            					expdata.value = new Expression(vardouble);
//            				}else if(var.getValue() instanceof Long){
//            					long varlong = Long.valueOf(var.getValue().toString());
//            					expdata.value = new Expression(varlong);
//            				}else if (var.getValue() instanceof PointerValue){
//            					PointerDomain pd=new PointerDomain((PointerValue) var.getValue());	
//            					SymbolFactor s=SymbolFactor.genSymbol(v.getType(), v.getImage());
//            					expdata.currentvex.addSymbolDomain(s, pd);
//            					expdata.value=new Expression(s);
//            				}else{
//            					expdata.value=new Expression(SymbolFactor.genSymbol(v.getType(),v.getImage()));
//            					
//            				}
//        				}else{
//        					expdata.value=new Expression(SymbolFactor.genSymbol(v.getType(),v.getImage()));
//        				}
//        			}else {
//        				SymbolFactor sym=SymbolFactor.genSymbol(v.getType(),v.getImage());
//        				//modified by zhouhb
//        				//处理形如f(a,b)中参数的初始化问题
//        				//remodified by zhouhb  2010/8/6
//        				//参数无需初始化
////        				if(v.getType() instanceof CType_Pointer&&node.jjtGetNumChildren()==0){
////    						PointerDomain p=new PointerDomain();
////    						expdata.currentvex.addSymbolDomain(sym, p);
////        				}
//        				expdata.value=new Expression(sym);
//        			}
        			//不用判断副作用
        			SymbolFactor sym=SymbolFactor.genSymbol(v.getType(),v.getImage());
					expdata.value=new Expression(sym);
        			if ( expdata.currentvex != null) {
        				if(v.getScope() instanceof SourceFileScope){
            				Variable var = Variable.getVariable(v);
            				//dyk 增加var.getType()!=null 的条件
            				if(var != null&&var.getType()!=null){
            					if(!var.getType().isArrayType()){
            						if(Config.USEUNKNOWN){
	            						Domain d = Domain.getUnknownDomain(Domain.getDomainTypeFromType(v.getType()));
	            					    expdata.currentvex.addSymbolDomain(sym,d);
            						}
	            					else
	        							expdata.currentvex.addSymbolDomain(sym,
	                							Domain.getFullDomainFromType(v.getType()));
            					}

            					else{
            						PointerDomain pd=new PointerDomain((PointerValue) PointerValue.NOTNULL);
            						expdata.currentvex.addSymbolDomain(sym, pd);
            					}
            				}
        				}
            				
        				expdata.currentvex.addValue(v, expdata.value);
        			}
        		}
        	}else if(decl instanceof MethodNameDeclaration){
        		MethodNameDeclaration mnd = (MethodNameDeclaration)decl;
        		Method method=null;
        		MethodSummary ms =null;
        		//库函数返回值处理 ssj
        		if(mnd != null && mnd.isLib()){
        	        InterContext interContext = InterContext.getInstance();
        	        Map<String, MethodNameDeclaration> libDecls = interContext.getLibMethodDecls();
        	        MethodNameDeclaration  libmethod=libDecls.get(mnd.getImage());
        	        if(libmethod!=null){
        	        	method = libmethod.getMethod();
        	        	if(method != null){
        	        		Domain d = method.getReturnDomain();
        	                SymbolFactor s = SymbolFactor.genSymbol(node.getType());
        	                if(Config.USEUNKNOWN && d==null)
        	                	d = Domain.getUnknownDomain(Domain.getDomainTypeFromType(node.getType()));
        	                node.getCurrentVexNode().addSymbolDomain(s, d);
        	                expdata.value=new Expression(s);
        	        	}    
        	        }
        	        //是库函数，但是没有摘要，则直接生成一个符号，其返回值区间为最大区间
        	        else if(Config.LIB_NOSUMMARY_NPD&&mnd.getType()!=null)
        	        {
        	        	if(mnd.getType() instanceof CType_Function&&((CType_Function)mnd.getType()).getReturntype()!=null)
        	        	{
        	        		CType returnType=((CType_Function)mnd.getType()).getReturntype();
        	        		if(returnType instanceof CType_Pointer)
        	        		{
        	        			SymbolFactor s=SymbolFactor.genSymbol(mnd.getType(),mnd.getImage());
        	        			node.getCurrentVexNode().addSymbolDomain(s, new PointerDomain(PointerValue.NULL_OR_NOTNULL));
        	        			expdata.value=new Expression(s);
        	        		}if(returnType instanceof CType_Pointer)
        	        		{
        	        			SymbolFactor s=SymbolFactor.genSymbol(mnd.getType(),mnd.getImage());
        	        			node.getCurrentVexNode().addSymbolDomain(s, new PointerDomain(PointerValue.NULL_OR_NOTNULL));
        	        			expdata.value=new Expression(s);
        	        		}
        	        		
        	        	}
        	        }
        	        if(expdata.value==null){
        	        	//是库函数，但是没有摘要，则直接生成一个符号，其返回值区间未知
        	        	expdata.value=new Expression(SymbolFactor.genSymbol(mnd.getType(),mnd.getImage()));
        	        }
        	    }else{
            		//chh  计算表达式中遇到函数调用时，对可以计算出函数返回值的函数，获取其返回值计算
        	    	if(mnd!=null)
            			method=mnd.getMethod();
            		if(method!=null&&method.getReturnDomain()!=null)
        			{
        				//整型域
            			if((method.getReturnDomain().getDomaintype()==DomainType.INTEGER)&&
        						(((IntegerDomain)method.getReturnDomain()).getMax()==((IntegerDomain)method.getReturnDomain()).getMin()))
        					expdata.value=new Expression(((IntegerDomain)method.getReturnDomain()).getMax());
        				//浮点域
            			else if((method.getReturnDomain().getDomaintype()==DomainType.DOUBLE)&&
        						(((DoubleDomain)method.getReturnDomain()).getMax()==((DoubleDomain)method.getReturnDomain()).getMin()))
        					expdata.value=new Expression(((DoubleDomain)method.getReturnDomain()).getMax());
            			else if(method.getReturnDomain().getDomaintype()==DomainType.POINTER){
            				CType type=node.getType();
                			CType pointer=null;
                			if(type!=null && type instanceof CType_Function){
                				pointer=((CType_Function)type).getReturntype();
                				if(pointer!=null && pointer instanceof CType_Pointer){
                					SymbolFactor s=SymbolFactor.genSymbol(type);
                					expdata.value=new Expression(s);
                					expdata.currentvex.addSymbolDomain(s, method.getReturnDomain());           				
                				}
                			}
            			}
            			else if(expdata.value == null){
            				CType type = method.getReturnType();
            				expdata.value=new Expression(SymbolFactor.genSymbol(type));
            			}
        			}else{//其他暂不处理
            			//zys:如果是指针类型的赋值，则添加其默认赋值为NULLORNOTNULL
            			CType type=node.getType();
            			CType pointer=null;
            			if(type!=null && type instanceof CType_Function){
            				pointer=((CType_Function)type).getReturntype();
            				//如果函数返回值类型为版本暂时处理不了类型，则不予处理，减少漏报
            				//add by zhouhb 2010/8/30
            				if(pointer!=null && pointer instanceof CType_Pointer&&!(((CType_Pointer)pointer).getOriginaltype() instanceof CType_BaseType)){
            					return data;
            				}
            				//end by zhouhb
            				if(pointer!=null && pointer instanceof CType_Pointer){
            					SymbolFactor s=SymbolFactor.genSymbol(type);
            					expdata.value=new Expression(s);
            					PointerDomain domain=new PointerDomain();
            					expdata.currentvex.addSymbolDomain(s, domain);
            				}
            			}
            			if(expdata.value==null){
            				expdata.value=new Expression(SymbolFactor.genSymbol(type));
            			}
            		}
            		//chh  计算表达式中遇到函数调用时，对可以计算出函数返回值的函数，获取其返回值计算 end
            		
            		//函数处理 针对全局变量后置条件处理 ssj
            		if(mnd!=null)
            			ms = mnd.getMethodSummary();
            		if(ms != null && !ms.getPostConditions().isEmpty()){
                		Set<MethodFeature> mtdpostcond = ms.getPostConditions();
               			for(MethodFeature mtdfea:mtdpostcond)
               			{
               				if(mtdfea instanceof MethodPostCondition) {
                    			MethodPostCondition mtdpost = (MethodPostCondition)mtdfea;
                				Map<Variable, Domain> msvariables = mtdpost.getPostConds();
                				for(Variable msvariable:msvariables.keySet())
                				{//zys:为后置条件中的变量生成新的符号表达式
                					VariableNameDeclaration v = (VariableNameDeclaration)Search.searchInVariableUpward(msvariable.getName(),scope);
                    					/**zys:函数摘要生成的疑问？
                    					 * 1、假定有file1.c与file2.c两个源文件都#include "file3.c"，
                    					 * 		且file3.c中仅有一个带有条件编译选项的函数
                    					 * 2、如果file1.c先分析，则由于条件编译的不同，生成了file1.c中该函数的摘要信息
                    					 * 3、当file2.c分析时遇到该函数调用，则首先获取之前生成的摘要，再按照本文件中的条件编译选项添加新的摘要
                    					 * 4、以上分析的结果就导致摘要信息在单个文件中找不到 */
                					if(v==null)
                    					continue;
                					SymbolFactor s=SymbolFactor.genSymbol(v.getType());
                    				Domain d=msvariables.get(msvariable);
                    				node.getCurrentVexNode().addSymbolDomain(s, d);
                					Expression expr=new Expression(s);
                    				node.getCurrentVexNode().addValue(v, expr);
                				}
               				}
                		}
                	}
        	    }
//        		 if(Config.USEUNKNOWN && expdata.value.getDomain(expdata.currentvex.getSymDomainset())==null)
//        			 expdata.currentvex.addSymbolDomain(expdata.value.getAllSymbol().iterator().next(),  Domain.getUnknownDomain(Domain.getDomainTypeFromType(node.getType())));
        	}
    	}
        return data;
    }
    

	public Object visit(ASTRelationalExpression node, Object data) {
		ExpressionVistorData expdata=(ExpressionVistorData)data;
		node.jjtGetChild(0).jjtAccept(this, expdata);
		Expression leftvalue=expdata.value;
		Expression rightvalue=null;
		DoubleDomain d1=null;
		DoubleDomain d2=null;
		try{
			//从左到右进行符号计算
			for (int i = 1; i < node.jjtGetNumChildren(); i++) {
				Node c = node.jjtGetChild(i);
				expdata.value = null;
				c.jjtAccept(this, expdata);
				rightvalue = expdata.value;
				
				if(leftvalue==null || rightvalue==null){
					throw new MyNullPointerException("RelationalExpression Value NULL in(.i) "+node.getBeginFileLine());
				}
				
				String operator = node.getOperatorType().get(i-1);
				d1=Domain.castToDoubleDomain(leftvalue.getDomain(expdata.currentvex.getSymDomainset()));
				d2=Domain.castToDoubleDomain(rightvalue.getDomain(expdata.currentvex.getSymDomainset()));
				if(d1==null || d2==null){
					throw new MyNullPointerException("RelationalExpression Domain NULL in(.i) "+node.getBeginFileLine());
				}
				if(Config.USEUNKNOWN && (d1.isUnknown() && d2.isUnknown())){
					throw new MyNullPointerException("RelationalExpression Domain UNKNOWN in(.i) "+node.getBeginFileLine());
				}
				if(operator.equals(">")){
					/**dongyk 20120306 判定循环是否至少一次*/
					/*if(expdata.currentvex.getLoopHead()&&d1.getIntervals().size()>0&&d2.getIntervals().size()>0&&(d1.getMin()>d2.getMax())){
						expdata.currentvex.setLoopExecuteAtleastOnce(true);
					}*/
					if(d1.getMin()>d2.getMax()){
						leftvalue=new Expression(1);
						continue;
					}else if(d1.getMax()<=d2.getMin()){
						leftvalue=new Expression(0);
						continue;
					}
				}else if(operator.equals(">=")){
					/**dongyk 20120306 判定循环是否至少一次*/
					/*if(expdata.currentvex.getLoopHead()&&d1.getIntervals().size()>0&&d2.getIntervals().size()>0&&(d1.getMin()>=d2.getMax())){
						expdata.currentvex.setLoopExecuteAtleastOnce(true);
					}*/
					if(d1.getMin()>=d2.getMax()){
						leftvalue=new Expression(1);
						continue;
					}else if(d1.getMax()<d2.getMin()){
						leftvalue=new Expression(0);
						continue;
					}
				}else if(operator.equals("<")){
					/**dongyk 20120306 判定循环是否至少一次*/
					/*if(expdata.currentvex.getLoopHead()&&d1.getIntervals().size()>0&&d2.getIntervals().size()>0&&(d1.getMax()<d2.getMin())){
						//expdata.currentvex.setLoopExecuteAtleastOnce(true);
					}*/
					if(d1.getMin()<d2.getMax()){
						leftvalue=new Expression(1);
						continue;
					}else if(d1.getMax()>=d2.getMin()){
						leftvalue=new Expression(0);
						continue;
					}
				}else if(operator.equals("<=")){
					/**dongyk 20120306 判定循环是否至少一次*/
					/*if(expdata.currentvex.getLoopHead()&&d1.getIntervals().size()>0&&d2.getIntervals().size()>0&&(d1.getMax()<=d2.getMin())){
						expdata.currentvex.setLoopExecuteAtleastOnce(true);
					}*/
					if(d1.getMin()<=d2.getMax()){
						leftvalue=new Expression(1);
						continue;
					}else if(d1.getMax()>d2.getMin()){
						leftvalue=new Expression(0);
						continue;
					}
				}
				throw new MyNullPointerException("RelationalExpression Domain Unknown in(.i) "+node.getBeginFileLine());
			}
		}catch(MyNullPointerException e){
			//super.visit(node,expdata);
			SymbolFactor sym=SymbolFactor.genSymbol(CType_BaseType.getBaseType("int"));
			expdata.currentvex.addSymbolDomain(sym, new IntegerDomain(0,1));
			leftvalue=new Expression(sym);
			expdata.value=leftvalue;
			return data;
		}
		
		expdata.value=leftvalue;
		return data;
	}
	
	public Object visit(ASTShiftExpression node, Object data) {
		return dealBinaryBitOperation(node,data,node.getOperators());
	}
	
	public Object visit(ASTUnaryExpression node, Object data) {
		ExpressionVistorData expdata=(ExpressionVistorData)data;
		if(node.jjtGetChild(0) instanceof ASTPostfixExpression){
			ExpressionVistorData expdata1=expdata;
			node.jjtGetChild(0).jjtAccept(this, expdata1);
			
			expdata.arrayIndex=expdata1.arrayIndex;
			return expdata;
		}else if(node.getOperatorType().size()==1){
			node.jjtGetChild(0).jjtAccept(this, expdata);
			if(node.getOperatorType().get(0).equals("++")){
				if(expdata.value==null){
					expdata.value=new Expression(1);
				}else{
					expdata.value=expdata.value.add(new Expression(1));
				}								
				ASTPrimaryExpression p = (ASTPrimaryExpression) ((SimpleNode)node.jjtGetChild(0)).getSingleChildofType(ASTPrimaryExpression.class);
				if(p!=null){
					VariableNameDeclaration v = p.getVariableDecl();
					if (v != null && expdata.sideeffect && expdata.currentvex != null) {
						expdata.currentvex.addValue(v, expdata.value);
					}
				}
				if(Config.Field){
					ASTPostfixExpression po=(ASTPostfixExpression) ((SimpleNode)node.jjtGetChild(0)).getSingleChildofType(ASTPostfixExpression.class);
					if(po!=null){
						VariableNameDeclaration v = po.getVariableDecl();
						if (v != null && expdata.sideeffect && expdata.currentvex != null&&expdata.value!=null) {
							expdata.currentvex.addValue(v, expdata.value);
						}
					}
				}
			}else{
				if(expdata.value==null){
					expdata.value=new Expression(1);
				}else{
					expdata.value=expdata.value.sub(new Expression(1));
				}				
				ASTPrimaryExpression p = (ASTPrimaryExpression) ((SimpleNode)node.jjtGetChild(0)).getSingleChildofType(ASTPrimaryExpression.class);
				if(p!=null){
					VariableNameDeclaration v = p.getVariableDecl();
					if (v != null && expdata.sideeffect && expdata.currentvex != null) {
						expdata.currentvex.addValue(v, expdata.value);
					}
				}
			}
			return data;
		}else if(node.jjtGetChild(0) instanceof ASTUnaryOperator){
			ASTUnaryOperator operator=(ASTUnaryOperator)node.jjtGetChild(0);
			String o=operator.getOperatorType().get(0);
			AbstractExpression castexpression=(AbstractExpression)node.jjtGetChild(1);
			node.jjtGetChild(1).jjtAccept(this, expdata);
			if(o.equals("&&")){
				//不知道怎么处理
			}//modified by zhouhb
			else if(o.equals("&")){
				SymbolFactor sym=SymbolFactor.genSymbol(node.getType());
				PointerDomain p=new PointerDomain();
				p.offsetRange=new IntegerDomain(0,0);
				//p.AllocType=CType_AllocType.stackType;
				if(p.Type.contains(CType_AllocType.NotNull)){
					p.Type.remove(CType_AllocType.NotNull);
				}
				p.Type.add(CType_AllocType.stackType);
				p.setValue(PointerValue.NOTNULL);
				p.setElementtype(castexpression.getType());
				expdata.currentvex.addSymbolDomain(sym, p);
				expdata.value=new Expression(sym);
				return data;
			}else if(o.equals("*")){
				//add by zhouhb
				//2011.12.15
				String image=node.getImage();
		    	if(!image.equals("")){
		    		//处理出现
		    		Scope scope=node.getScope();
		        	NameDeclaration decl=Search.searchInVariableAndMethodUpward(image, scope);
		        	if(decl instanceof VariableNameDeclaration){
		        		//变量处理
		        		VariableNameDeclaration v=(VariableNameDeclaration)decl;
		        		expdata.value=expdata.currentvex.getValue(v);
		        	}
		        	if(expdata.value==null){
		        		
		        	}
		        	return data;
		        		//end by zhouhb
		        	}
			}else if(o.equals("+")){
				//不处理
			}else if(o.equals("-")){
				if(expdata.value!=null){
					expdata.value=new Expression(0).sub(expdata.value);
				}else{
					SymbolFactor sym=SymbolFactor.genSymbol(CType_BaseType.getBaseType("int"));
					expdata.currentvex.addSymbolDomain(sym, new IntegerDomain(0,1));
					expdata.value=new Expression(sym);
				}
				return data;
			}else if(o.equals("~")){
				if(expdata.value==null)
				{
					return data;
				}
				IntegerDomain i=Domain.castToIntegerDomain(expdata.value.getDomain(expdata.currentvex.getSymDomainset()));
				if(i!=null&&i.isCanonical()){
					expdata.value=new Expression(new IntegerFactor(~i.getMin()));
					return data;
				}
			}else if(o.equals("!")){
				if(expdata.value==null){
					SymbolFactor sym=SymbolFactor.genSymbol(CType_BaseType.getBaseType("int"));
					expdata.currentvex.addSymbolDomain(sym, new IntegerDomain(0,1));
					expdata.value=new Expression(sym);
					return data;
				}
				IntegerDomain i=Domain.castToIntegerDomain(expdata.value.getDomain(expdata.currentvex.getSymDomainset()));
				if(i!=null){
					if(i.isCanonical()&&i.getMin()==0){
						expdata.value=new Expression(1);
						return data;
					}else if(!i.contains(0)){
						expdata.value=new Expression(0);
						return data;
					}else{
						SymbolFactor sym=SymbolFactor.genSymbol(CType_BaseType.getBaseType("int"));
						expdata.currentvex.addSymbolDomain(sym, new IntegerDomain(0,1));
						expdata.value=new Expression(sym);
						return data;
					}
				}
			}else{
				throw new RuntimeException("ASTUnaryOperator error!");
			}
		}else if(node.getImage().equals("sizeof")){
			node.jjtGetChild(0).jjtAccept(this, expdata);		
			ASTConstant con = (ASTConstant)node.getSingleChildofType(ASTConstant.class);
        	if(node.jjtGetChild(0) instanceof ASTTypeName){
				ASTTypeName typeName=(ASTTypeName)node.jjtGetChild(0);
				if(typeName.getType()!=null){
					expdata.value=new Expression(typeName.getType().getSize());
					return data;
				}
			}if(con != null){
				//liuli 2010.8.13 添加对sizeof ("qwefff");这种情况的处理
				Domain ret = expdata.value.getDomain(con.getCurrentVexNode().getSymDomainset());
				if(ret != null && ret instanceof PointerDomain){
					PointerDomain p = (PointerDomain)ret;
					long i = p.getLen(p);
					expdata.value=new Expression(i);
					return data;
				}
			}else{
				//liuli：sizeof的参数有可能为自定义的类型，在语法树中并不当做ASTTypeName识别
				Scope scope=node.getScope();
				String image = ((ASTUnaryExpression)node.jjtGetChild(0)).getImage();
	        	NameDeclaration decl=Search.searchInVariableUpward(image, scope);
	        	if(decl != null && decl.getType()!=null){
					expdata.value=new Expression(decl.getType().getSize());
					return data;
				}
	        	//end
				AbstractExpression child=(AbstractExpression)node.jjtGetChild(0);
				if(child.getType()!=null){
					if(child.getFirstChildOfType(ASTFieldId.class)!=null && ((AbstractExpression)child.getFirstChildOfType(ASTFieldId.class)).getType()!=null)
						child = (AbstractExpression) child.getFirstChildOfType(ASTFieldId.class);
					expdata.value=new Expression(child.getType().getSize());
					return data;
				}
			}
		}else if(node.getImage().contains("alignof")){
			//不知道怎么处理
		}else if(node.getImage().contains("real")){
			//不知道怎么处理
		}else if(node.getImage().contains("imag")){
			//不知道怎么处理
		}else{
			//不知道怎么处理
		}
		expdata.value=new Expression(SymbolFactor.genSymbol(node.getType()));
		return data;
	}
		
	private Object dealBinaryBitOperation(AbstractExpression node, Object data,String op) {
		ExpressionVistorData expdata=(ExpressionVistorData)data;
		node.jjtGetChild(0).jjtAccept(this, expdata);
		Expression leftvalue=expdata.value;
		Expression rightvalue=null;
		try{
			//从左到右进行符号计算
			for (int i = 1; i < node.jjtGetNumChildren(); i++) {
				Node c = node.jjtGetChild(i);
				c.jjtAccept(this, expdata);
				rightvalue = expdata.value;
				
				if(leftvalue==null || rightvalue==null){
					throw new MyNullPointerException("BinaryBitOperation Value NULL in(.i) "+node.getBeginFileLine());
				}
				
				IntegerDomain i1=Domain.castToIntegerDomain(leftvalue.getDomain(expdata.currentvex.getSymDomainset()));
				IntegerDomain i2=Domain.castToIntegerDomain(rightvalue.getDomain(expdata.currentvex.getSymDomainset()));
				if(i1==null || i2==null){
					throw new MyNullPointerException("BinaryBitOperation Domain NULL in(.i) "+node.getBeginFileLine());
				}
				
				//如果不能确定计算出值，直接产生一个抽象取值未定的符号，返回
				if(i1!=null&&i2!=null&&i1.isCanonical()&&i2.isCanonical()){
					long temp=0;
					if(op.equals("&")){
						temp=i1.getMin()&i2.getMin();
					}else if(op.equals("|")){
						temp=i1.getMin()|i2.getMin();
					}else if(op.equals("^")){
						temp=i1.getMin()^i2.getMin();
					}else if(op.equals(">>")){
						temp=i1.getMin()>>i2.getMin();
					}else if(op.equals("<<")){
						temp=i1.getMin()<<i2.getMin();
					}else if(op.equals("%")){
						temp=i1.getMin()%i2.getMin();
					}
					leftvalue=new Expression(new IntegerFactor(temp));
				}
				else if(i1!=null&&!i1.contains(0)&&i2!=null&&!i2.contains(0)&&op.equals("&"))
				{
					if(i1.getMin()>0||i2.getMin()>0)
					{
						SymbolFactor sym=SymbolFactor.genSymbol(CType_BaseType.getBaseType("int"));
						expdata.currentvex.addSymbolDomain(sym, new IntegerDomain(1,IntegerDomain.DEFAULT_MAX));
						leftvalue=new Expression(sym);
					}
					else
						throw new MyNullPointerException("BinaryBitOperation Domain Unknown in(.i) "+node.getBeginFileLine());
					
				}
				else{
					throw new MyNullPointerException("BinaryBitOperation Domain Unknown in(.i) "+node.getBeginFileLine());
				}
			}
		}catch(MyNullPointerException e){
			super.visit(node,expdata);
			SymbolFactor sym=SymbolFactor.genSymbol(CType_BaseType.getBaseType("int"));
			if(Config.USEUNKNOWN)
				expdata.currentvex.addSymbolDomain(sym, IntegerDomain.getUnknownDomain());
			else
				expdata.currentvex.addSymbolDomain(sym, IntegerDomain.getFullDomain());
			leftvalue=new Expression(sym);
			expdata.value=leftvalue;
			return data;
		}
		expdata.value=leftvalue;
		return data;
	}
	
	static Logger logger=Logger.getRootLogger();
	class MyNullPointerException extends Exception{
		public MyNullPointerException(String msg){
			//logger.info("捕获自定义异常："+msg);
		}
	}
}
