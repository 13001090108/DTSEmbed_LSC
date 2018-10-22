package softtest.symboltable.c;

import java.util.*;
import softtest.config.c.*;
import softtest.interpro.c.InterContext;
import softtest.ast.c.*;
import softtest.symboltable.c.Type.*;

public class OccurrenceAndExpressionTypeFinder extends CParserVisitorAdapter {
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
	
	/**
	 * @author zys	2010.2.1
	 * <p>
	 * 处理在声明的同时赋值的情况，如int i=1;此时应该添加一次NameOccurence
	 * </p>
	 */
	public Object visit(ASTDirectDeclarator node,Object data)
	{
		super.visit(node, data);
		SimpleNode declarator=(SimpleNode)node.jjtGetParent();
		if(declarator instanceof ASTDeclarator && declarator.getNextSibling() instanceof ASTInitializer)
		{
        	VariableNameDeclaration decl=new VariableNameDeclaration(node);
        	NameOccurrence occ=new NameOccurrence(decl,node,node.getImage());
        	decl.getScope().addNameOccurrence(decl, occ);
        	node.setType(decl.getType());
		}
		return data;
	}
	
	public Object visit(ASTAdditiveExpression node, Object data) {
		super.visit(node, data);
		CType current = null;
		for (int i = 0; i < node.jjtGetNumChildren(); i++) {
			AbstractExpression abst = (AbstractExpression)node.jjtGetChild(i);
			if (current == null) {
				current = abst.getType();
			} else {
				current = castBaseType( current, abst.getType()); 
			}
		}
		node.setType(current);
		return data;
	}
	
	public Object visit(ASTANDExpression node, Object data) {
		super.visit(node, data);
		//node.setType(CType_BaseType.intType);
		//当对有符号数和无符号数进行与运算时，进行无符号提升
		//原处理是均做整型处理，相当不精确；现在区别有无符号整型，暂时对char,short,long,long long未进行细致区分
		//add by zhouhb
		//2011.3.15
		List<Node> li=node.findChildrenOfType(ASTUnaryExpression.class);
		if(!li.isEmpty()){
			for(Node unary:li)
			{
				if(((ASTUnaryExpression)unary).getType()!=null&&((ASTUnaryExpression)unary).getType().isUnsignedType()){
					node.setType(CType_BaseType.uIntType);
					break;
				}else{
					node.setType(CType_BaseType.intType);
				}
			}
		}else{
			node.setType(CType_BaseType.intType);
		}
		
		return data;
	}
	
	public Object visit(ASTArgumentExpressionList node, Object data) {
		//在ASTPostfixExpression中统一处理
		return super.visit(node, data);
	}
	
	public Object visit(ASTAssignmentExpression node, Object data) {
		super.visit(node, data);
		node.jjtGetChild(0);
		Node absNode=node.jjtGetChild(0);
		if(!(absNode instanceof AbstractExpression))
		{
			absNode=node.jjtGetChild(1);
		}
		if(absNode!=null&&absNode instanceof AbstractExpression)
		{
			AbstractExpression abst = (AbstractExpression)absNode;
			node.setType(abst.getType());
			node.setImage(abst.getImage());
		}
		return data;
	}
	
	public Object visit(ASTCastExpression node, Object data) {
		super.visit(node, data);
		if(node.jjtGetChild(0) instanceof ASTTypeName){
			ASTTypeName typename=(ASTTypeName)node.jjtGetChild(0);
			node.setType(typename.getType());
		}else{//由于void CastExpression() #CastExpression(>1): {}所以不会生成单支树，所以代码冗余了
			throw new RuntimeException("ASTCastExpression can't generate single child");
		}
		return data;
	}


	public Object visit(ASTConditionalExpression node, Object data) {
		super.visit(node, data);
		//由于void ConditionalExpression() #ConditionalExpression(>1): {}所以不会生成单支树，所以代码冗余了
		if (node.jjtGetNumChildren() == 1) {
			throw new RuntimeException("ASTConditionalExpression can't generate single child");
		} else {
			AbstractExpression abst = (AbstractExpression)node.jjtGetChild(1);
			node.setType(abst.getType());
		}
		return data;
	}
	
	public Object visit(ASTConstant node, Object data) {
		String image = node.getImage();
		if (image.startsWith("\"")) {
			node.setType(CType_Pointer.CPPString);
		} else if(image.startsWith("\'")) {
			node.setType(CType_BaseType.charType);
		} else {
			boolean isInteger = false;
			if (image.endsWith("l") || image.endsWith("L")||
				image.endsWith("u") || image.endsWith("U")) {
				image = image.substring(0, image.length() - 1);
			}
			char[] source = image.toCharArray();
			int length = source.length;
			int intValue = 0;
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
				intValue = (int) computeValue;
				isInteger = true;
			} catch (RuntimeException e) {
			}
			
			//zys:根据常量的后缀字符判断该常量的实际类型，目前的判断尚不完善，甚至有错。。。2010.1.14
			if (isInteger) {
				image = node.getImage();
				if (image.endsWith("ull") || image.endsWith("ULL")
						|| image.endsWith("llu") || image.endsWith("LLU")) {
					node.setType(CType_BaseType.uLongLongType);
				} else if (image.endsWith("ul") || image.endsWith("lu")
						|| image.endsWith("UL") || image.endsWith("LU")) {
					node.setType(CType_BaseType.uLongType);
				} else if (image.endsWith("ll") || image.endsWith("LL")) {
					node.setType(CType_BaseType.longLongType);
				} else if (image.endsWith("u") || image.endsWith("U")) {
					node.setType(CType_BaseType.uIntType);
				}else{
					node.setType(CType_BaseType.intType);
				}
			} else if(image.equalsIgnoreCase("true") || image.equalsIgnoreCase("false")) {
				node.setType(CType_BaseType.boolType);
			} else {
				if (image.endsWith("f") || image.endsWith("F")) 
				{
					node.setType(CType_BaseType.floatType);
				}else 
				{
					node.setType(CType_BaseType.doubleType);
				}
			}
		}
		return data;
	}

	
	public Object visit(ASTConstantExpression node, Object data) {
		super.visit(node, data);
		AbstractExpression abst = (AbstractExpression)node.jjtGetChild(0);
		node.setType(abst.getType());
		return data;
	}

	public Object visit(ASTEqualityExpression node, Object data) {
		super.visit(node, data);
		node.setType(CType_BaseType.boolType);
		return data;
	}
	
	public Object visit(ASTExclusiveORExpression node, Object data) {
		super.visit(node, data);
		node.setType(CType_BaseType.intType);
		return data;
	}
	
	public Object visit(ASTExpression node, Object data) {
		super.visit(node, data);
		AbstractExpression abst = (AbstractExpression)node.jjtGetChild(0);
		node.setType(abst.getType());
		node.setImage(abst.getImage());
		return data;
	}
	
	public Object visit(ASTFieldId node, Object data) {
		//在ASTPostfixExpression中统一处理
		return super.visit(node, data);
	}
	
	public Object visit(ASTInclusiveORExpression node, Object data) {
		super.visit(node, data);
		node.setType(CType_BaseType.intType);
		return data;
	}
	
	public Object visit(ASTLogicalANDExpression node, Object data) {
		super.visit(node, data);
		node.setType(CType_BaseType.boolType);
		return data;
	}
	
	public Object visit(ASTLogicalORExpression node, Object data) {
		super.visit(node, data);
		node.setType(CType_BaseType.boolType);
		return data;
	}
	
	public Object visit(ASTMultiplicativeExpression node, Object data) {
		super.visit(node, data);
		CType current = null;
		for (int i = 0; i < node.jjtGetNumChildren(); i++) {
			AbstractExpression abst = (AbstractExpression)node.jjtGetChild(i);
			if (current == null) {
				current = abst.getType();
			} else {
				current = castBaseType(current, abst.getType()); 
			}
		}
		node.setType(current);
		return data;
	}
	
	public Object visit(ASTPostfixExpression node, Object data) {
		ASTPrimaryExpression primary=(ASTPrimaryExpression)node.jjtGetChild(0);
		primary.jjtAccept(this, data);
		ArrayList<Boolean> flags=node.getFlags();
		ArrayList<String> operators=node.getOperatorType();
		CType current=primary.getType();
		String image = primary.getImage();
		node.setImage(image);
		
		NameDeclaration declPrimary=Search.searchInVariableAndMethodUpward(node.getImage(), node.getScope());
		if(declPrimary!=null)
		{
			node.setDecl(declPrimary);
		}
		
		if(current==null)//处理库函数调用的情况，如printf();目前将库函数的返回值暂时设置为int
		{
			current=CType_BaseType.intType;
			node.setType(current);			
		}
		int j=1;
		int arrayIndex=0;
		String arrImage=image;
		for(int i=0;i<flags.size();i++){
			boolean flag=flags.get(i);
			String operator=operators.get(i);
			if(operator.equals("[")){
				arrImage=arrImage+"[0]";
				ASTExpression expression =null;
				if(flag){
					expression=(ASTExpression)node.jjtGetChild(j++);
					expression.jjtAccept(this, data);
					if(Config.Field){
						//dongyk 20120413
						//对多维数组下标的处理
						ASTExpression exp=(ASTExpression)node.findDirectChildOfType(ASTExpression.class).get(arrayIndex);			
						List<Node> primaryNodes=exp.findChildrenOfType(ASTPrimaryExpression.class);	
						arrayIndex++;
						if(primaryNodes.size()==1&&((ASTPrimaryExpression)primaryNodes.get(0)).jjtGetNumChildren()==1
									&&((ASTPrimaryExpression)primaryNodes.get(0)).jjtGetChild(0) instanceof ASTConstant)
						{   /*dongyk 20120413处理数组下标是常量的情况*/
							ASTPrimaryExpression primaryNode=(ASTPrimaryExpression)primaryNodes.get(0);
							if(primaryNode.jjtGetNumChildren()==1&&primaryNode.jjtGetChild(0) instanceof ASTConstant)
							{
								ASTConstant con=(ASTConstant)primaryNode.jjtGetChild(0);
								image=image+"["+con.getImage()+"]";
								node.setImage(image);
								
								Scope scope=node.getScope();
					        	NameDeclaration decl=Search.searchInVariableAndMethodUpward(node.getImage(), scope);
					        	if(decl!=null && (decl.getType() instanceof CType_AbstPointer||decl.getType().equals(CType.getOrignType(current)))){
				        			NameOccurrence occ=new NameOccurrence(decl,node,node.getImage());
				            		decl.getScope().addNameOccurrence(decl, occ);
				            		node.setDecl(decl);
					        	}else
					        	{					        		
					        		VariableNameDeclaration newdecl =new VariableNameDeclaration(node);
					        		newdecl.setFatherVariable(node.getDecl());
									newdecl.setType(CType.getOneOrignType(current));
									scope.addDeclaration(newdecl);
									node.setDecl(newdecl);
					        	}
							}
						}else  /*dongyk 20120413 处理数组下标是非常量的情况*/
						{
							String strImage=image;
							Scope scope=node.getScope();
							image=image+"[exp"+scope.getVarIndex()+"]";
							node.setImage(image);		
							
							VariableNameDeclaration decl = new VariableNameDeclaration(node.getFileName(),scope,image,node);							
							NameDeclaration decl0=Search.searchInVariableAndMethodUpward(arrImage, scope);
							if(decl0!=null&&decl0 instanceof VariableNameDeclaration)
							{
								VariableNameDeclaration decl00=(VariableNameDeclaration)decl0;
								decl.setFatherVariable(node.getDecl());
								decl.setType(decl00.getType());
								scope.addDeclaration(decl);
								NameOccurrence occ=new NameOccurrence(decl00,node,strImage);
								scope.addNameOccurrence(decl, occ);
								node.setDecl(decl);
							}else if(decl0==null)
							{
								arrImage=arrImage.substring(0,arrImage.lastIndexOf("["));								
								decl0=Search.searchInVariableAndMethodUpward(arrImage, scope);
								if(decl0!=null&&decl0 instanceof VariableNameDeclaration)
								{
									VariableNameDeclaration decl00=(VariableNameDeclaration)decl0;
									if(decl00.getType() instanceof CType_AbstPointer)
									{
										CType_AbstPointer typePointer=(CType_AbstPointer)decl00.getType();
										decl.setFatherVariable(node.getDecl());
										decl.setType(typePointer.getOriginaltype());
										scope.addDeclaration(decl);
										NameOccurrence occ=new NameOccurrence(decl00,node,strImage);
										scope.addNameOccurrence(decl, occ);
										node.setDecl(decl);
									}
								}
							}
						}
					}
				}else{
					throw new RuntimeException("ASTPostfixExpression error!");
				}
				CType atype=current.getSimpleType();
				if(atype instanceof CType_AbstPointer){
					CType_AbstPointer ptype=(CType_AbstPointer) atype;
					current=ptype.getOriginaltype();
				}
//				if(Config.Field){
//					VariableNameDeclaration decl = new VariableNameDeclaration(node);
//					Scope s = ((SimpleNode) node.jjtGetParent()).getScope();
//					//对于a.b这样的表达式已经在结构体声明的时候声明完，如果作用域中已存在该变量，则不添加
//					if(Search.searchInVariableUpward(decl.image, s)==null){
//						s.addDeclaration(decl);
//						node.setDecl(decl);
//					}
//				}
			}else if(operator.equals("(")){
				ASTArgumentExpressionList expressionlist=null;
				if(flag){
					expressionlist=(ASTArgumentExpressionList)node.jjtGetChild(j++);
					expressionlist.jjtAccept(this, data);
				}
				CType atype=current.getSimpleType();
				if(atype instanceof CType_Function){
					CType_Function ptype=(CType_Function) atype;
					current=ptype.getReturntype();
					if(flag){
						expressionlist.setType(current);
					}
				}
			}else if(operator.equals(".")){
				ASTFieldId field=null;
				if(flag){
					field=(ASTFieldId)node.jjtGetChild(j++);
					field.jjtAccept(this, data);
				}else{
					throw new RuntimeException("ASTPostfixExpression error!");
				}
				CType atype=current.getSimpleType();
				CType ftype=findFieldTypeAndOcc(atype,field);
				if(ftype!=null){
					field.setType(ftype);
					current=ftype;
				}
				if(Config.Field){
					image=image+"."+field.getImage();
					arrImage=arrImage+"."+field.getImage();
					node.setImage(image);
					Scope s = ((SimpleNode) node.jjtGetParent()).getScope();
	        		NameDeclaration decl=Search.searchInVariableAndMethodUpward(node.getImage(), s);
					if(decl==null){
						VariableNameDeclaration newdecl =new VariableNameDeclaration(node);
						newdecl.setFatherVariable(node.getDecl());
						newdecl.setType(current);
						s.addDeclaration(newdecl);
						node.setDecl(newdecl);
					}else{
						node.setDecl(decl);
					}
				}
			}else if(operator.equals("->")){
				ASTFieldId field=null;
				if(flag){
					field=(ASTFieldId)node.jjtGetChild(j++);
					field.jjtAccept(this, data);
				}else{
					throw new RuntimeException("ASTPostfixExpression error!");
				}
				CType atype=current.getSimpleType();
				if(atype instanceof CType_Pointer){
					CType_Pointer ptype=(CType_Pointer)atype;
					atype=ptype.getOriginaltype().getSimpleType();
					CType ftype=findFieldTypeAndOcc(atype,field);
					if(ftype!=null){
						field.setType(ftype);
						current=ftype;
					}
					if(Config.Field){
						image=image+"->"+field.getImage();
						arrImage=arrImage+"->"+field.getImage();
						node.setImage(image);
						Scope s = ((SimpleNode) node.jjtGetParent()).getScope();
		        		NameDeclaration decl=Search.searchInVariableAndMethodUpward(node.getImage(), s);
						if(decl==null){
							VariableNameDeclaration newdecl =new VariableNameDeclaration(node);
							newdecl.setFatherVariable(node.getDecl());
							newdecl.setType(current);
							s.addDeclaration(newdecl);
							node.setDecl(newdecl);
						}else{
							node.setDecl(decl);
						}
					}
				}
			}else{
				//do nothing
			}
		}
		node.setType(current);
		return data;
	}
	
    @Override
	public Object visit(ASTPrimaryExpression node, Object data) {
    	super.visit(node, data);
    	if(node.jjtGetNumChildren()>0 && node.jjtGetChild(0) instanceof ASTExpression)
    	{
    		ASTExpression expr=(ASTExpression)node.jjtGetChild(0);
    		node.setImage(expr.getImage());
    		//zys:2010.8.12 双重指针
    		/**struct {int i;}**s;	f(){int k=(*s)->i;} */
    		if(expr.getType()!=null){
    			node.setType(expr.getType());
    		}
    	}
    	String image=node.getImage();
    	if(!image.equals("")){
    		//处理出现
    		Scope scope=node.getScope();
        	NameDeclaration decl=Search.searchInVariableAndMethodUpward(image, scope);
        	if(decl!=null && node.jjtGetNumChildren()==0){
        		if(decl.getType() instanceof CType_Array){
        			//如果为数组类型，则回退到上一节点将变量出现添加进去
        		}else{
        			NameOccurrence occ=new NameOccurrence(decl,node,image);
            		decl.getScope().addNameOccurrence(decl, occ);
        		}
            	if(node.getType()==null)
            	{
            		node.setType(decl.getType());
            	}
        	}else if(Config.USE_SUMMARY && node.isMethod()){
        		//zys 2011.6.24 malloc printf等库函数可以在无函数原型时任意调用，因此节点类型应该取库函数返回值类型
        		MethodNameDeclaration mnd=InterContext.getInstance().getLibMethodDecls().get(node.getImage());
        		if(mnd!=null)
        			node.setType(mnd.getType());
        	}else if(node.getType()==null){
        		//zys:2010.7.23	typedef char gchar;i=sizeof(gchar);
        		CType type=scope.getType(image);
        		node.setType(type);
        	}
    	}else if(node.jjtGetChild(0) instanceof ASTCompoundStatement){
    		ASTCompoundStatement compound=(ASTCompoundStatement)node.jjtGetChild(0) ;
    		if(compound.jjtGetNumChildren()>0){
    			SimpleNode somelist=(SimpleNode)compound.jjtGetChild(0);
    			SimpleNode somenode=(SimpleNode)somelist.jjtGetChild(somelist.jjtGetNumChildren()-1);
    			AbstractExpression child=(AbstractExpression)somenode.getFirstChildInstanceofType(AbstractExpression.class);
    			if(child!=null){
    				node.setType(child.getType());
    			}else{
    				node.setType(CType_BaseType.getBaseType("void"));
    			}
    		}
    		
    	}else{
    		AbstractExpression child=(AbstractExpression)node.jjtGetChild(0);
    		node.setType(child.getType());
    	}
    	
        return data;
    }
	
	public Object visit(ASTRelationalExpression node, Object data) {
		super.visit(node, data);
		node.setType(CType_BaseType.boolType);
		return data;
	}
	
	public Object visit(ASTShiftExpression node, Object data) {
		super.visit(node, data);
		AbstractExpression abst = (AbstractExpression)node.jjtGetChild(0);
		if (abst.getType() == CType_BaseType.uIntType) {
			node.setType(CType_BaseType.uIntType);
		} else {
			node.setType(CType_BaseType.intType);
		}
		return data;
	}
	
	public Object visit(ASTUnaryExpression node, Object data) {
		super.visit(node, data);
		if(node.jjtGetChild(0) instanceof ASTPostfixExpression){
			ASTPostfixExpression postfixexpression=(ASTPostfixExpression)node.jjtGetChild(0);
			node.setType(postfixexpression.getType());
			//zys:
			node.setImage(postfixexpression.getImage());
		}else if(node.getOperatorType().size()==1){
			ASTUnaryExpression unnaryexpression=(ASTUnaryExpression)node.jjtGetChild(0);
			node.setType(unnaryexpression.getType()); 
		}else if(node.jjtGetChild(0) instanceof ASTUnaryOperator){
			ASTUnaryOperator operator=(ASTUnaryOperator)node.jjtGetChild(0);
			String o=operator.getOperatorType().get(0);
			AbstractExpression castexpression=(AbstractExpression)node.jjtGetChild(1);
			if(o.equals("&&")){
				//不知道怎么处理，先暂时弄成整型
				node.setType(CType_BaseType.uIntType);
			}else if(o.equals("&")){
				CType type=castexpression.getType();
				if(type!=null){
					CType_Pointer ptype=new CType_Pointer();
					ptype.setOriginaltype(type);
					CType_Qualified qtype=new CType_Qualified(ptype);
					qtype.addQualifier("const");
					node.setType(qtype);
				}
			}else if(o.equals("*")){
				CType type=castexpression.getType();
				if(type!=null&&type.getSimpleType() instanceof CType_Pointer){
					CType_Pointer ptype=(CType_Pointer)type.getSimpleType();
					node.setType(ptype.getOriginaltype());
					//modified by zhouhb
					if(Config.Field){
						String image=castexpression.getImage();						
						node.setImage("*"+image+"");
						//dongyk
						CType baseType=ptype.getOriginaltype();
									
						Scope s = ((SimpleNode) node.jjtGetParent()).getScope();
		        		NameDeclaration decl=Search.searchInVariableAndMethodUpward(node.getImage(), s);
						if(decl==null){
							VariableNameDeclaration newdecl =new VariableNameDeclaration(node);
							newdecl.setType(baseType);
							s.addDeclaration(newdecl);
							node.setDecl(newdecl);
						}else{
							node.setDecl(decl);
						}
						
					}else{
						node.setImage(castexpression.getImage());
					}
					//end by zhouhb
					//zys:为函数指针形式的函数调用建立函数使用		(*funP)();
//					Scope scope=node.getScope();
//					ASTPrimaryExpression exp=(ASTPrimaryExpression)(castexpression.getFirstChildOfType(ASTPrimaryExpression.class));
//					String image=exp.getImage();
//		        	NameDeclaration decl=Search.searchInVariableAndMethodUpward(image, scope);
//		        	if(decl!=null){
//		        		NameOccurrence occ=new NameOccurrence(decl,node,image);
//		        		//ZYS 2010.3.14	作用域内变量出现的添加通过最底层节点进行，否则会出现重复添加的情况！
//		        		//decl.getScope().addNameOccurrence(decl, occ);
//		        		node.setType(decl.getType());
//		        	}
				}else if(type!=null&&type.getSimpleType() instanceof CType_Array){
					CType_Array ptype=(CType_Array)type.getSimpleType();
					node.setType(ptype.getOriginaltype());
				}
			}else if(o.equals("+")){
				node.setType(CType_BaseType.intType);
			}else if(o.equals("-")){
				node.setType(CType_BaseType.intType);
			}else if(o.equals("~")){
				node.setType(CType_BaseType.intType);
			}else if(o.equals("!")){
				node.setType(CType_BaseType.boolType);
			}else{
				throw new RuntimeException("ASTUnaryOperator error!");
			}
			
		}else if(node.getImage().equals("sizeof")){
			node.setType(CType_BaseType.uIntType);
		}else if(node.getImage().contains("alignof")){
			node.setType(CType_BaseType.uIntType);
		}else if(node.getImage().contains("real")){
			node.setType(CType_BaseType.doubleType);
		}else if(node.getImage().contains("imag")){
			node.setType(CType_BaseType.doubleType);
		}else{
			//不知道怎么处理，先暂时弄成整型
			//LOOKAHEAD("{" InitializerList() "}") "{" InitializerList() "}"
			node.setType(CType_BaseType.uIntType);
		}
		
		return data;
	}
	
	private CType castBaseType(CType ltype, CType rtype) {
		if (!(ltype instanceof CType_BaseType) || !(rtype instanceof CType_BaseType)) {
			if (ltype == null || rtype == null) {
				return CType_BaseType.intType;
			}
			if (ltype.isPointType()) {
				return ltype;
			}
			if(rtype.isPointType()){
				return rtype;
			}
			return CType_BaseType.intType;
		}
		
		// double type convert
		if (ltype == CType_BaseType.longDoubleType || rtype == CType_BaseType.longDoubleType) {
			return CType_BaseType.longDoubleType;
		} else if (ltype == CType_BaseType.doubleType || rtype == CType_BaseType.doubleType) {
			return CType_BaseType.doubleType;
		} else if (ltype == CType_BaseType.floatType || rtype == CType_BaseType.floatType) {
			return CType_BaseType.floatType;
		} 
		if (ltype == CType_BaseType.uLongLongType || rtype == CType_BaseType.uLongLongType) {
			return CType_BaseType.uLongLongType;
		} else if (ltype == CType_BaseType.longLongType || rtype == CType_BaseType.longLongType) {
			return CType_BaseType.longLongType;
		}
		
		// integeral promotion
		ltype = promoteToint(ltype);
		rtype = promoteToint(rtype);
		
		// convert
		if (ltype == CType_BaseType.uLongType || rtype == CType_BaseType.uLongType) {
			return CType_BaseType.uLongType; 
		} else if (ltype == CType_BaseType.uIntType || rtype == CType_BaseType.uIntType) {
			return CType_BaseType.uIntType;
		}else if (ltype == CType_BaseType.longType || rtype == CType_BaseType.longType) {
			return CType_BaseType.longType;
		} else {
			return CType_BaseType.intType;
		}
	}
	
	private CType promoteToint(CType type) {
		if (type == CType_BaseType.boolType 
			|| type == CType_BaseType.charType
			|| type == CType_BaseType.uCharType
			|| type == CType_BaseType.shortType 
			|| type == CType_BaseType.uShortType) {
			return CType_BaseType.intType;
		}
		return type;
	}
	
	private CType findFieldTypeAndOcc(CType type,ASTFieldId field){
		CType ret=null;
		if(type instanceof CType_Struct || type instanceof CType_Union){
			ClassNameDeclaration typedecl=(ClassNameDeclaration)Search.searchInClassUpward(type.getName(), field.getScope());
			if(typedecl!=null){
				Scope s=typedecl.getNode().getScope();
				VariableNameDeclaration vardecl=(VariableNameDeclaration)Search.searchInVariableUpward(field.getImage(),s);
				if(vardecl!=null){
					field.setVariableNameDeclaration(vardecl);
					NameOccurrence occ=new NameOccurrence(vardecl,field,field.getImage());
					vardecl.getScope().addNameOccurrence(vardecl, occ);
					ret=vardecl.getType();
				}
			}
		}
		return ret;
	}
}
