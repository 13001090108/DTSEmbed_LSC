package softtest.rules.gcc.fault;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import softtest.ast.c.ASTAdditiveExpression;
import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTCastExpression;
import softtest.ast.c.ASTConstant;
import softtest.ast.c.ASTExpression;
import softtest.ast.c.ASTFieldId;
import softtest.ast.c.ASTFunctionDefinition;
import softtest.ast.c.ASTLogicalANDExpression;
import softtest.ast.c.ASTMultiplicativeExpression;
import softtest.ast.c.ASTPostfixExpression;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTStatement;
import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.ASTUnaryOperator;
import softtest.ast.c.Node;
import softtest.ast.c.SimpleNode;
import softtest.ast.c.AbstractExpression;
import softtest.cfg.c.VexNode;
import softtest.config.c.Config;
import softtest.domain.c.analysis.ConditionData;
import softtest.domain.c.analysis.ConditionDomainVisitor;
import softtest.domain.c.analysis.ExpressionValueVisitor;
import softtest.domain.c.analysis.ExpressionVistorData;
import softtest.domain.c.analysis.SymbolDomainSet;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.IntegerDomain;
import softtest.domain.c.interval.IntegerInterval;
import softtest.domain.c.interval.PointerDomain;
import softtest.domain.c.interval.PointerValue;
import softtest.domain.c.symbolic.Expression;
import softtest.domain.c.symbolic.SymbolFactor;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.Method;
import softtest.rules.c.BasicStateMachine;
import softtest.rules.c.StateMachineUtils;
import softtest.summary.gcc.fault.MethodNPDPreConditionVisitor;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.NameDeclaration;
import softtest.symboltable.c.Scope;
import softtest.symboltable.c.Search;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.Type.CType;
import softtest.symboltable.c.Type.CType_AbstPointer;
import softtest.symboltable.c.Type.CType_Array;
import softtest.symboltable.c.Type.CType_Pointer;
import softtest.symboltable.c.Type.CType_Function;
import softtest.symboltable.c.Type.CType_BaseType;;

/**
 * 处理指针表达式的NPD_EXP错误
 * 处理形如：
 * 1）st->i,str.i,结构体变量的空指针引用错误
 * 2）...
 */
public class NPD_ExpStateMachine extends BasicStateMachine {
	
	@Override
	public void registFetureVisitors() {
		super.registFetureVisitors();
		InterContext.addPreConditionVisitor(MethodNPDPreConditionVisitor.getInstance());
	}

	public static List<FSMMachineInstance> createNPD_ExpStateMachines(SimpleNode node, FSMMachine fsm) {
		
		List<FSMMachineInstance> list = new ArrayList<FSMMachineInstance>();

		String xPath1 = ".//AssignmentExpression//UnaryExpression[/UnaryOperator[@Operators='*']]";
		List<SimpleNode> nodes1 = StateMachineUtils.getEvaluationResults(node, xPath1);
		for (SimpleNode snode : nodes1) {
			ASTUnaryExpression unarynode = (ASTUnaryExpression)snode;
			String StrExp = null;
			ASTAdditiveExpression additiveExp = (ASTAdditiveExpression)unarynode.getFirstChildOfType(ASTAdditiveExpression.class);
			FSMMachineInstance fsmInstance = fsm.creatInstance();
			ASTPrimaryExpression pExp = null;
			NameDeclaration decl = null;
			if(additiveExp != null )//加号表达式*(a+b)
			{
				StrExp = getExpStr((SimpleNode)additiveExp.jjtGetParent());
				pExp =(ASTPrimaryExpression)additiveExp.getFirstChildOfType(ASTPrimaryExpression.class);	
				decl = pExp.getVariableDecl();
			}
			//*p,*func(),**p
			else
			{								
				StrExp = getExpStr(unarynode);
				
			    pExp = (ASTPrimaryExpression)unarynode.getFirstChildOfType(ASTPrimaryExpression.class);
			    
			    //ytang  *p去掉			    
			    if(!pExp.isMethod()){
				    ASTUnaryExpression unode = (ASTUnaryExpression)unarynode.getFirstChildOfType(ASTUnaryExpression.class);
				    if(!(unode.getImage().contains(".") || unode.getImage().contains("->")|| unode.getImage().contains("*")|| unode.getImage().contains("[")))
						continue;
			    }
			    
			    //if(!(unarynode.getImage().contains(".") || unarynode.getImage().contains("->")|| unarynode.getImage().contains("*")|| unarynode.getImage().contains("[")))
				//	continue;
			    if(unarynode.jjtGetNumChildren()==2&&unarynode.jjtGetChild(1) instanceof ASTUnaryExpression)
			    {
			    	ASTUnaryExpression uChild = (ASTUnaryExpression)unarynode.jjtGetChild(1);
			    	decl  = uChild.getVariableDecl();
			    }else
			    {
			    	decl = pExp.getVariableDecl();
			    }
				
			
			}
			if(pExp != null && !pExp.isMethod())
			{
				
				if (decl instanceof VariableNameDeclaration) {
					VariableNameDeclaration vDecl = (VariableNameDeclaration) decl;
					CType type = vDecl.getType();
					if( type != null && type.isPointType() )
						fsmInstance.setRelatedVariable(vDecl);
					else
						continue;
				}
			}
			else if(pExp != null && pExp.isMethod())  //函数表达式,*func()
			{
				NameDeclaration decl1 = null;
				decl1 = pExp.getMethodDecl();
				
				if(decl1!=null)
				{
					CType type = decl1.getType();
					if( type != null && (type instanceof CType_Function))
					{
						CType_Function funType=(CType_Function)type;
						CType returnType = funType.getReturntype();
						if( returnType != null && returnType.isPointType() )
							fsmInstance.setRelatedVariable(	new VariableNameDeclaration(unarynode));
					}
				}
				else if(decl!=null && decl instanceof VariableNameDeclaration)
				{
					fsmInstance.setRelatedVariable((VariableNameDeclaration)decl);
				}
			}	
			fsmInstance.setRelatedASTNode(unarynode);
			fsmInstance.setResultString(StrExp);
			list.add(fsmInstance);			
		}
		
		
		//对于形如(p+i)[0],fun()[0],(p+i)->ptr,s.str[0]
		String xPath3 = ".//AssignmentExpression//UnaryExpression/PostfixExpression[./PrimaryExpression][ends-with(@Operators,'[') or ends-with(@Operators,'[ .') or ends-with(@Operators,'->')]";
		List<SimpleNode> nodes3 = StateMachineUtils.getEvaluationResults(node, xPath3);
		for (SimpleNode snode : nodes3) {
			ASTPostfixExpression postnode = (ASTPostfixExpression)snode;
			ASTPrimaryExpression primExp = (ASTPrimaryExpression)postnode.getFirstChildOfType(ASTPrimaryExpression.class);
			String StrExp = null;
			ASTAdditiveExpression additiveExp = (ASTAdditiveExpression)primExp.getSingleChildofType(ASTAdditiveExpression.class);
			FSMMachineInstance fsmInstance = fsm.creatInstance();
			boolean fsmFlag=true;
									
			if(additiveExp != null ){
				StrExp = getExpStr((SimpleNode)additiveExp.jjtGetParent());
				fsmInstance.setResultString(StrExp);
			}	
			else if(!primExp.isMethod())
			{
				if( !(postnode.getImage().contains(".") || postnode.getImage().contains("->") ||postnode.getImage().contains("[")) || postnode.jjtGetNumChildren() < 2)
				{
					continue;
				}
				//ytang add
				if(postnode.jjtGetNumChildren()<3 && primExp.jjtGetNumChildren()==0)
					continue;
				
				//dongyk 2012 04 10
				//处理由  ->与 [  构成的多级指针
				ArrayList<Boolean> flags=postnode.getFlags();
				ArrayList<String> operators=postnode.getOperatorType();
				
				Scope localScope = postnode.getScope();
				int operatorIndex=0;
				
				boolean arrayFlag=true;
				
				for(int i=0;i<flags.size();i++){
					boolean flag=flags.get(i);
					String operator=operators.get(flags.size()-i-1);
					if(operator.equals("[")){
						String image=postnode.getImage();
						operatorIndex=image.indexOf("[", operatorIndex);
						if(operatorIndex>0)
						{							
							image=image.substring(0, operatorIndex);
							operatorIndex++;
							NameDeclaration decl=Search.searchInVariableAndMethodUpward(image, localScope);
				        								
							if(decl!=null && (decl.getType() instanceof CType_Array||decl.getType() instanceof CType_Pointer)){
				        		VariableNameDeclaration v=(VariableNameDeclaration)decl;			        		
				        		FSMMachineInstance arrayFsmInstance = fsm.creatInstance();
				        		arrayFsmInstance.setRelatedASTNode(postnode);	
				        		arrayFsmInstance.setRelatedVariable(v);
				    			list.add(arrayFsmInstance);
				    			fsmFlag=false;
				        	}	
							
							//dongyk 2012.4.12 处理可能不合理，需要完善   有问题，如果decl是函数，则不能是VariableNameDeclaration，而是MethodNameDeclaration
							//而且 重点看的是其返回指，而不是函数
							//解决思路，对函数返回 捏造一个 返回质类型的变量。
							if(decl!=null && decl.getType() instanceof CType_Function){
								VariableNameDeclaration v=null;
								if(decl instanceof MethodNameDeclaration)
								{
									v=new VariableNameDeclaration(postnode);
									
								}else
								{
				        			v=(VariableNameDeclaration)decl;
								}
								CType returnType=((CType_Function)decl.getType()).getReturntype();				        		
				        		if(returnType instanceof CType_Pointer)
				        		{
				        			FSMMachineInstance arrayFsmInstance = fsm.creatInstance();
					        		arrayFsmInstance.setRelatedASTNode(postnode);	
					        		arrayFsmInstance.setRelatedVariable(v);
					    			list.add(arrayFsmInstance);
					    			fsmFlag=false;
				        		}			        		
				        	}
						}else
						{
							
							if(arrayFlag&&postnode.jjtGetChild(1)!=null &&postnode.jjtGetChild(1) instanceof ASTExpression)
							{
								
								ASTExpression expressionNode=(ASTExpression)postnode.getFirstDirectChildOfType(ASTExpression.class);
								if(expressionNode!=null)
								{
									ExpressionVistorData exprdata = new ExpressionVistorData();
									exprdata.currentvex=expressionNode.getCurrentVexNode();
									exprdata.sideeffect=true;
									
									ExpressionValueVisitor eVisitor=new ExpressionValueVisitor();
									exprdata=(ExpressionVistorData)eVisitor.visit((ASTAssignmentExpression)expressionNode.getFirstDirectChildOfType(ASTAssignmentExpression.class), exprdata);									
									if(exprdata.value==null)
									{
										//宏替换的 形如 ""[text[i]],直接不处理
										//System.out.println("NPD-EXP 238:"+expressionNode.getFileName());
									}else
									{
										Domain domain=exprdata.value.getDomain(exprdata.currentvex.getSymDomainset());
										IntegerDomain vDomain=Domain.castToIntegerDomain(domain);
										if(vDomain!=null)
										{
											
											//
											List<Integer> intNums=vDomain.getNums();
											for(int intN=0;intN<intNums.size();intN++)
											{
												int index=intNums.get(intN).intValue();
												String arrImage=primExp.getImage()+"["+index+"]";
												NameDeclaration declArrar=Search.searchInVariableAndMethodUpward(arrImage, localScope);
												
												if(declArrar!=null&&declArrar.getType() instanceof CType_Pointer)
												{
													VariableNameDeclaration vArray=(VariableNameDeclaration)declArrar;
													FSMMachineInstance arrayFsmInstance = fsm.creatInstance();
									        		arrayFsmInstance.setRelatedASTNode(postnode);	
									        		arrayFsmInstance.setRelatedVariable(vArray);
									    			list.add(arrayFsmInstance);
												}else
												{
													break;
												}
												
											}
										}
									}
								}
							}
						}
					}else if(operator.equals("->")){
						String image=postnode.getImage();
						operatorIndex=image.indexOf("->", operatorIndex);
						if(operatorIndex>0)
						{
							image=image.substring(0, operatorIndex);
							operatorIndex+=2;
							NameDeclaration decl=Search.searchInVariableAndMethodUpward(image, localScope);
				        	if(decl!=null && decl.getType() instanceof CType_Pointer){
				        		VariableNameDeclaration v=(VariableNameDeclaration)decl;			        		
				        		FSMMachineInstance structFsmInstance = fsm.creatInstance();
				        		structFsmInstance.setRelatedASTNode(postnode);	
				        		structFsmInstance.setRelatedVariable(v);
				    			list.add(structFsmInstance);
				    			fsmFlag=false;
				        	}
				        	
				        	//dongyk 2012.4.12 处理可能不合理，需要完善
				        	if(decl!=null && decl.getType() instanceof CType_Function){
				        		MethodNameDeclaration v=(MethodNameDeclaration)decl;
				        		CType_Function funType=(CType_Function)v.getType();
				        		if(funType.getReturntype() instanceof CType_Pointer)
				        		{
				        			FSMMachineInstance arrayFsmInstance = fsm.creatInstance();
					        		arrayFsmInstance.setRelatedASTNode(postnode);	
					        		//arrayFsmInstance.setRelatedVariable(v);
					    			list.add(arrayFsmInstance);
					    			fsmFlag=false;
				        		}			        		
				        	}
						}
					}									
				}
			}
			if(fsmFlag)
			{
				fsmInstance.setRelatedASTNode(postnode);			
				list.add(fsmInstance);
			}
		}

		return list;

	}
	
	
	
	
	/**
	 * 根据抽象语法树节点，确定表达式的内容
	 */
	
	private static String getExpStr(SimpleNode node ) {
		if (node instanceof ASTUnaryExpression) {
			ASTUnaryExpression unaryExp = (ASTUnaryExpression) node;
			return unaryExp.getImage();
		}
		else if(node instanceof ASTAssignmentExpression){
			String exp = null;
			if(node.jjtGetNumChildren() == 1 && node.jjtGetChild(0) instanceof ASTAdditiveExpression){
				ASTAdditiveExpression additive = (ASTAdditiveExpression)node.jjtGetChild(0);
				if(additive.jjtGetNumChildren() == 2 ){
					ASTUnaryExpression child1=null,child2=null;
					if(additive.jjtGetChild(0) instanceof ASTCastExpression)
					{
						child1=(ASTUnaryExpression)((SimpleNode)additive.jjtGetChild(0)).getFirstDirectChildOfType(ASTUnaryExpression.class);
					}else if(additive.jjtGetChild(0) instanceof ASTUnaryExpression)
					{
						child1 = (ASTUnaryExpression)additive.jjtGetChild(0);
					}
					if(additive.jjtGetChild(1) instanceof ASTCastExpression)
					{
						child2=(ASTUnaryExpression)((SimpleNode)additive.jjtGetChild(1)).getFirstDirectChildOfType(ASTUnaryExpression.class);
					}else if(additive.jjtGetChild(1) instanceof ASTUnaryExpression)
					{
						child2 = (ASTUnaryExpression)additive.jjtGetChild(1);
					}
					if(child1.getSingleChildofType(ASTConstant.class) != null)
						exp = ((ASTConstant)child1.getSingleChildofType(ASTConstant.class)).getImage();
					else if(child1.getSingleChildofType(ASTPrimaryExpression.class) != null)
						exp = ((ASTPrimaryExpression)child1.getSingleChildofType(ASTPrimaryExpression.class)).getImage();
					exp += additive.getOperators();
					if(child2!=null&&child2.getSingleChildofType(ASTConstant.class) != null)
						exp += ((ASTConstant)child2.getSingleChildofType(ASTConstant.class)).getImage();
					else if(child2!=null&&child2.getSingleChildofType(ASTPrimaryExpression.class) != null)
						exp += ((ASTPrimaryExpression)child2.getSingleChildofType(ASTPrimaryExpression.class)).getImage();				
				}
			}
			return exp;
		}
		return null;
	}
	
	private static String getExpStr(SimpleNode node, int num){
		if(node instanceof ASTPostfixExpression){
			ASTPostfixExpression postnode = (ASTPostfixExpression)node;
			ArrayList<String> ops = postnode.getOperatorType();
			String exp = null;
			int size = ops.size();
			int childnum = postnode.jjtGetNumChildren();
			if(size != childnum -1 )
				return null;
			exp = ((AbstractExpression)postnode.jjtGetChild(0)).getImage();
			if(num > 1)
				exp += ops.get(0);
			int i;
			for( i = 1; i < num  ; i++){
				exp += ((AbstractExpression)postnode.jjtGetChild(i)).getImage();
				if( i != num -1 )
				    exp += ops.get(i - 1);
			}			
			return exp;
		}
		return null;
	}
	
	/**
	 * 检测当前的指针表达式的区间是否可能为空
	 * @param nodes
	 * @param fsmin
	 * @return
	 */
	public static boolean checkNPDExp(List nodes, FSMMachineInstance fsmin) {
		boolean isError = false;
		Iterator listIter = nodes.iterator();
		while (listIter.hasNext()) {
			SimpleNode node = (SimpleNode) listIter.next();
			if (fsmin.getRelatedASTNode() != node) {
				continue;
			}
			
			PointerDomain mydomain = null;					
			
			ASTPrimaryExpression pExp = null;
			pExp = (ASTPrimaryExpression)node.getFirstChildOfType(ASTPrimaryExpression.class);
			
			ASTAdditiveExpression additiveExp = null;
			additiveExp = (ASTAdditiveExpression)pExp.getFirstChildOfType(ASTAdditiveExpression.class);
			ASTPrimaryExpression pExp1 = null;
			if(additiveExp != null && additiveExp.getFirstChildOfType(ASTPrimaryExpression.class)!=null)
				pExp1 = (ASTPrimaryExpression)additiveExp.getFirstChildOfType(ASTPrimaryExpression.class);
			if(pExp1!=null && (!pExp1.isMethod())){//*(p+i),(p+i)[0],(p+i)->str
					AbstractExpression assign = (AbstractExpression)additiveExp.jjtGetParent();
					if(assign.getCurrentVexNode()== null)
						continue; 
					ExpressionValueVisitor expvst = new ExpressionValueVisitor();
					ExpressionVistorData visitdata = new ExpressionVistorData();
					Domain expdomain = null;
		
					visitdata.currentvex = assign.getCurrentVexNode();	
					visitdata.currentvex.setfsmCompute(true);
					expvst.visit((SimpleNode)(assign), visitdata);	
					visitdata.currentvex.setfsmCompute(false);
					expdomain = visitdata.value.getDomain(visitdata.currentvex.getLastsymboldomainset());
					if(expdomain != null && expdomain instanceof PointerDomain)
						mydomain= (PointerDomain)expdomain;
					else if(expdomain != null && expdomain instanceof IntegerDomain)
					{
						mydomain=(PointerDomain)(Domain.castToType(expdomain, new CType_Pointer()));
					}
	//			
			}	
		  //针对测试用例  zbase =*(strrchr (\"hello world\", 'o') + 1) 进行处理
			else if(pExp!=null && pExp1!=null && pExp1.isMethod())
			{
				MethodNameDeclaration methodDecl = (MethodNameDeclaration)pExp1.getMethodDecl();
					if (methodDecl != null && methodDecl.getMethod() != null) {
						Method method = methodDecl.getMethod();
						if (Config.USE_SUMMARY)
							if (method.getReturnDomain() instanceof PointerDomain) 
								mydomain = (PointerDomain)method.getReturnDomain();
							else if(method.getReturnDomain() instanceof IntegerDomain)
								mydomain = (PointerDomain)Domain.castToType((IntegerDomain)method.getReturnDomain(),new CType_Pointer());
					}else if(fsmin.getRelatedVariable()!=null)
					{
						VexNode vex = node.getCurrentVexNode();
						boolean flag = vex.isFsmCompute();
						vex.setfsmCompute(true);
						mydomain = (PointerDomain)vex.getDomain(fsmin.getRelatedVariable());
						vex.setfsmCompute(flag);
					}
				
			}	
			else if( pExp != null && pExp.isMethod())
			{
				MethodNameDeclaration methodDecl = (MethodNameDeclaration)pExp.getMethodDecl();
				if (methodDecl != null && methodDecl.getMethod() != null) {
					Method method = methodDecl.getMethod();
					if (Config.USE_SUMMARY)
						if (method.getReturnDomain() instanceof PointerDomain) 
							mydomain = (PointerDomain)method.getReturnDomain();
						else if(method.getReturnDomain() instanceof IntegerDomain)
							mydomain = (PointerDomain)Domain.castToType((IntegerDomain)method.getReturnDomain(),new CType_Pointer());
				}
			}
			else if( node instanceof ASTUnaryExpression ){
				ASTUnaryExpression unaryExp = (ASTUnaryExpression)node;
				//指针变量的解，引用*p,*(A.i)
				if(fsmin.getRelatedVariable() != null)
				{
					if(fsmin.getRelatedVariable().getImage().indexOf("[-")>-1)
					{
						ExpressionVistorData exprdata = new ExpressionVistorData();
						exprdata.currentvex=unaryExp.getCurrentVexNode();
						exprdata.sideeffect=true;

						ExpressionValueVisitor eVisitor=new ExpressionValueVisitor();
						exprdata=(ExpressionVistorData)eVisitor.visit((ASTAssignmentExpression)unaryExp.getFirstChildOfType(ASTAssignmentExpression.class), exprdata);									
						Domain domain=exprdata.value.getDomain(exprdata.currentvex.getSymDomainset());
						IntegerDomain vDomain=Domain.castToIntegerDomain(domain);

						VariableNameDeclaration array = null;
						String arrImage=fsmin.getRelatedVariable().getImage();
						arrImage=arrImage.substring(0, arrImage.indexOf("[exp"));
						NameDeclaration declArr=Search.searchInVariableAndMethodUpward(arrImage, node.getScope());
						if (declArr instanceof VariableNameDeclaration) {
							array = (VariableNameDeclaration) declArr;
						}
						if(array.getType() instanceof CType_Pointer)
						{
							VexNode vex = node.getCurrentVexNode();
							Domain d = vex.getDomain(array);
							if( d!=null){
								if(d instanceof PointerDomain)
									mydomain = (PointerDomain)d;
								if(d instanceof IntegerDomain)
									mydomain = (PointerDomain)Domain.castToType(d,new CType_Pointer());							
							}
							break;
						}
						CType_Array temp = (CType_Array) array.getType();
						long length=temp.getDimSize();
						IntegerDomain arrDomain=new IntegerDomain(new IntegerInterval(0,length));
						if(vDomain==null)
						{
							vDomain=arrDomain;
						}else
						{
							vDomain=IntegerDomain.intersect(arrDomain, vDomain);
						}
						List<Integer> intNums=vDomain.getNums();
						for(int intN=0;intN<intNums.size();intN++)
						{
							int index=intNums.get(intN).intValue();

							ASTPrimaryExpression primExp=(ASTPrimaryExpression)unaryExp.getFirstChildOfType(ASTPrimaryExpression.class);

							String arrImages=primExp.getImage()+"["+index+"]";
							NameDeclaration declArrar=Search.searchInVariableAndMethodUpward(arrImages, unaryExp.getScope());

							if(declArrar!=null&&declArrar.getType() instanceof CType_Pointer)
							{
								VariableNameDeclaration vArray=(VariableNameDeclaration)declArrar;
								VexNode vex = unaryExp.getCurrentVexNode();
								Domain d = vex.getDomain(vArray);
								if( d!=null&& d instanceof PointerDomain ){
									if(mydomain==null)
									{
										mydomain=(PointerDomain)d;
									}else
									{
										mydomain = PointerDomain.union(mydomain, (PointerDomain)d);
									}

									if(mydomain.getValue()==PointerValue.NULL||mydomain.getValue()==PointerValue.NULL_OR_NOTNULL)
									{
										break;
									}
								}

							}else
							{
								break;
							}
						}
					}else
					{
						VexNode vex = unaryExp.getCurrentVexNode();
						boolean flag = vex.isFsmCompute();
						vex.setfsmCompute(true);
						Domain d = vex.getDomain(fsmin.getRelatedVariable());
						vex.setfsmCompute(flag);
						if(d instanceof PointerDomain)
							mydomain = (PointerDomain)d;
						if(d instanceof IntegerDomain)
							mydomain = (PointerDomain)Domain.castToType(d,new CType_Pointer());
					}	
				}	
			}

			else if(node instanceof ASTPostfixExpression ){
				//s.str[0],s->s1->str
				ASTPostfixExpression postfix = (ASTPostfixExpression)node;
				int num = postfix.jjtGetNumChildren();
				if( pExp != null && !pExp.isMethod())// (*p)->a[0];
				{
					NameDeclaration decl = null;					
					decl = pExp.getVariableDecl();
					if (decl instanceof VariableNameDeclaration) {						
						VariableNameDeclaration vDecl = (VariableNameDeclaration) decl;
						if(fsmin.getRelatedVariable()!=null)
						{
							vDecl=fsmin.getRelatedVariable();
							//非常量表达式处理开始

							if(fsmin.getRelatedVariable().getImage().indexOf("[-")>-1)
							{
								ExpressionVistorData exprdata = new ExpressionVistorData();
								exprdata.currentvex=node.getCurrentVexNode();
								exprdata.sideeffect=true;

								ExpressionValueVisitor eVisitor=new ExpressionValueVisitor();
								exprdata=(ExpressionVistorData)eVisitor.visit((ASTAssignmentExpression)node.getFirstChildOfType(ASTAssignmentExpression.class), exprdata);									
								Domain domain=exprdata.value.getDomain(exprdata.currentvex.getSymDomainset());
								IntegerDomain vDomain=Domain.castToIntegerDomain(domain);								

								VariableNameDeclaration array = null;
								String arrImage=fsmin.getRelatedVariable().getImage();
								arrImage=arrImage.substring(0, arrImage.indexOf("[-"));
								NameDeclaration declArr=Search.searchInVariableAndMethodUpward(arrImage, node.getScope());
								if (declArr instanceof VariableNameDeclaration) {
									array = (VariableNameDeclaration) declArr;
								}
								if(array.getType() instanceof CType_Pointer)
								{
									VexNode vex = node.getCurrentVexNode();
									Domain d = vex.getDomain(array);
									if( d!=null ){
										if(d instanceof PointerDomain)
											mydomain = (PointerDomain)d;
										if(d instanceof IntegerDomain)
											mydomain = (PointerDomain)Domain.castToType(d,new CType_Pointer());										
									}
									break;
								}
								CType_Array temp = (CType_Array) array.getType();
								long length=temp.getDimSize();
								IntegerDomain arrDomain=new IntegerDomain(new IntegerInterval(0,length));
								if(vDomain==null)
								{
									vDomain=arrDomain;
								}else
								{
									vDomain=IntegerDomain.intersect(arrDomain, vDomain);
								}
								List<Integer> intNums=vDomain.getNums();
								for(int intN=0;intN<intNums.size();intN++)
								{
									int index=intNums.get(intN).intValue();

									ASTPrimaryExpression primExp=(ASTPrimaryExpression)node.getFirstChildOfType(ASTPrimaryExpression.class);

									String arrImages=primExp.getImage()+"["+index+"]";
									NameDeclaration declArrar=Search.searchInVariableAndMethodUpward(arrImages, node.getScope());

									if(declArrar!=null&&declArrar.getType() instanceof CType_Pointer)
									{
										VariableNameDeclaration vArray=(VariableNameDeclaration)declArrar;
										VexNode vex = node.getCurrentVexNode();
										Domain d = vex.getDomain(vArray);
										if( d!=null&& d instanceof PointerDomain ){
											if(mydomain==null)
											{
												mydomain=(PointerDomain)d;
											}else
											{
												mydomain = PointerDomain.union(mydomain, (PointerDomain)d);
											}

											if(mydomain.getValue()==PointerValue.NULL||mydomain.getValue()==PointerValue.NULL_OR_NOTNULL)
											{
												break;
											}
										}

									}else
									{
										break;
									}
								}
							}


							//非常量表达式处理结束
						}
						CType type = vDecl.getType();
						if( type != null && type.isPointType() ){
							VexNode vex = pExp.getCurrentVexNode();
							Domain d = vex.getDomain(vDecl);
							if( d!=null&&d instanceof PointerDomain ){
								mydomain = (PointerDomain)d;
								fsmin.setResultString(pExp.getImage());
								if( mydomain != null && (mydomain.getValue() == PointerValue.NULL || mydomain.getValue() == PointerValue.NULL_OR_NOTNULL))
									isError = true;
								if(isError)
								{
									fsmin.setDesp(fsmin.getResultString()+ " 可能为空指针，被解引用");
									return isError;
								}
							}
						}
					}
				}
				for(int i = 1; i < num; i++){//s.str[0]形式
					String strExp = getExpStr(postfix, i);
					SimpleNode funcnode = (SimpleNode)postfix.getFirstParentOfType(ASTFunctionDefinition.class);
					String xPath0 = ".//AssignmentExpression/UnaryExpression/PostfixExpression[@Image = '"+strExp+"']";
					List<SimpleNode> nodes0 = StateMachineUtils.getEvaluationResults(funcnode, xPath0);
					Iterator liter = nodes0.iterator();
					if (liter.hasNext()) {
						ASTPostfixExpression postNode = (ASTPostfixExpression)liter.next();
						NameDeclaration decl = null;
						decl = postNode.getVariableDecl();
						if (decl instanceof VariableNameDeclaration) {
							VariableNameDeclaration vDecl = (VariableNameDeclaration) decl;
							CType type = vDecl.getType();
							if( type != null && type.isPointType() ){
								VexNode vex = postfix.getCurrentVexNode();
								vex.setfsmCompute(true);
								Domain d = vex.getDomain(vDecl);
								if( d instanceof PointerDomain ){
									mydomain = (PointerDomain)d;
									fsmin.setResultString(strExp);
									break;
								}
							}
						}
					}
				}				
			}else if(node instanceof ASTPrimaryExpression)
			{
				ASTPrimaryExpression primaryExp = (ASTPrimaryExpression)node;
				//指针变量的解，引用*p,*(A.i)
				if(fsmin.getRelatedVariable() != null)
				{

					VexNode vex = primaryExp.getCurrentVexNode();
					Domain d = vex.getDomain(fsmin.getRelatedVariable());
					if(d!=null){
						if(d instanceof PointerDomain)
						    mydomain = (PointerDomain)d;
						if(d instanceof IntegerDomain)
							mydomain = (PointerDomain)Domain.castToType(d,new CType_Pointer());
					}	
				}

			}

			if( mydomain != null && (mydomain.getValue() == PointerValue.NULL || mydomain.getValue() == PointerValue.NULL_OR_NOTNULL))
				isError = true;
			if(isError && fsmin.getRelatedVariable()!= null){
				if(!confirmNPD(node,fsmin.getRelatedVariable()))
					isError = false;
			}
			if(isError)
				fsmin.setDesp(fsmin.getResultString()+ " 可能为空指针，被解引用");
		}
		return isError;
	}

	public static boolean confirmNPD(SimpleNode idExp, VariableNameDeclaration vDecl) {
		// 检查表达式短路: if (p!=null && *p==1) 或者 if (p && *p==1)
		ASTLogicalANDExpression expressionAnd = (ASTLogicalANDExpression)idExp.getFirstParentOfType(ASTLogicalANDExpression.class);
		if (expressionAnd != null && expressionAnd.jjtGetNumChildren() >= 2) {
			for (int i = 0; i < expressionAnd.jjtGetNumChildren(); i++) {
				SimpleNode expNode = (SimpleNode)expressionAnd.jjtGetChild(i);
				if (idExp.isSelOrAncestor(expNode)) {
					break;
				}
				
				// p 的may集合是不是为非空
				ConditionDomainVisitor condVisitor = new ConditionDomainVisitor();
				ConditionData condData = new ConditionData(idExp.getCurrentVexNode());
				expNode.jjtAccept(condVisitor, condData);
				if (idExp.getCurrentVexNode().getValue(vDecl) == null || idExp.getCurrentVexNode().getValue(vDecl).getSingleFactor() == null) {
					continue;
				}
				if (!(idExp.getCurrentVexNode().getValue(vDecl).getSingleFactor() instanceof SymbolFactor)) {
					continue;
				}
				Domain pDomain = condData.getMayDomain((SymbolFactor) idExp.getCurrentVexNode().getValue(vDecl).getSingleFactor());
				if (pDomain != null && !pDomain.isUnknown() && pDomain instanceof PointerDomain) {
					PointerDomain point = (PointerDomain)pDomain;
					if( point.getValue() == PointerValue.NOTNULL || point.getValue() == PointerValue.NULL_OR_NOTNULL)
						return false;
				}
			}
		}
		// 确保不是sizeof(*p)
		boolean isSizeof = false;
		SimpleNode node = (SimpleNode)idExp.jjtGetParent();
		while (!(node instanceof ASTStatement) && node.jjtGetNumChildren() <= 2) {
			if (node instanceof ASTUnaryExpression && node.getImage().equals("sizeof")) {
				isSizeof = true;
				break;
			} else if (node instanceof ASTAssignmentExpression && node.jjtGetNumChildren() >= 2) {
				break;
			}
			node = (SimpleNode)node.jjtGetParent();
		}
		if (isSizeof) {
			return false;
		}
		return true;
	}

}