package softtest.summary.gcc.fault;



import java.util.List;
import java.util.Set;


import softtest.ast.c.ASTAdditiveExpression;
import softtest.ast.c.ASTCompoundStatement;
import softtest.ast.c.ASTConstant;
import softtest.ast.c.ASTExpression;
import softtest.ast.c.ASTPostfixExpression;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.CParserVisitorAdapter;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.VexNode;
import softtest.config.c.Config;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.Variable;
import softtest.interpro.c.ScopeType;
import softtest.rules.c.StateMachineUtils;
import softtest.rules.gcc.fault.BOStateMachine;
import softtest.rules.gcc.fault.BO.BOFunction;
import softtest.rules.gcc.fault.BO.BOHelper;
import softtest.rules.gcc.fault.BO.BOType;
import softtest.summary.c.MethodFeatureVisitor;
import softtest.summary.c.MethodSummary;

import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.NameDeclaration;
import softtest.symboltable.c.Search;
import softtest.symboltable.c.SourceFileScope;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.Type.CType;
import softtest.symboltable.c.Type.CType_AbstPointer;



/**
 * 记录BO函数摘要的动作类
 * @author chh
 */
public class MethodBOPreConditionVisitor  extends CParserVisitorAdapter implements MethodFeatureVisitor {
	private static MethodBOPreConditionVisitor instance;
	
	private MethodBOPreConditionVisitor(){
	}
	
	MethodNameDeclaration methodDecl = null;
	
	public static MethodBOPreConditionVisitor getInstance(){
		if(instance == null){
			instance = new MethodBOPreConditionVisitor();
		}
		return instance;
	}
	//访问函数结点，计算函数摘要
	public void visit(VexNode vexNode) {
		SimpleNode node = vexNode.getTreenode();
		if (node == null) {
			return;
		}
		MethodBOPreCondition feature = new MethodBOPreCondition();
		
		methodDecl = InterContext.getMethodDecl(vexNode);
		if (methodDecl != null) {
			node.jjtAccept(this, feature);
		}
		if (feature.isEmpty()) {
			return;
		}
		
		// 将计算出的函数特性添加到函数摘要中
		MethodSummary summary = InterContext.getMethodSummary(vexNode);
		if (summary != null) {
			summary.addPreCondition(feature);
			if (Config.INTER_METHOD_TRACE) {
				if (methodDecl != null) {
					System.err.println(methodDecl.getFullName() + " " + feature);
				}
			}
		}
	}

	/**
	 * 确定当前变量是否存在BO前置约束
	 * @param bufDomain
	 * @param srcDecl
	 * @param feature
	 */
	private void confirmBOVar(long size, VariableNameDeclaration bufDecl, StringBuffer despmet,  MethodBOPreCondition feature,boolean flag) {
		Variable v = Variable.getVariable(bufDecl);
		StringBuffer despbuf = new StringBuffer("目标缓冲区："+bufDecl.getImage()+"；");
		if (v == null){
			//既不是参数也不是外部变量，只能是函数内部定义的局部变量//暂时只解决一维数组
				SimpleNode srcNode=bufDecl.getNode();
				ASTPrimaryExpression pNode=(ASTPrimaryExpression) srcNode.getSingleChildofType(ASTPrimaryExpression.class);
				if(pNode==null||pNode.jjtGetNumChildren()!=0)
					return ;
				else{
					VariableNameDeclaration src=pNode.getVariableDecl();
					v=Variable.getVariable(src);
					if(v==null)
						return ;
				}
		}
			
		
		if (feature.contains(bufDecl)) {//如果已经  存在，比较区间，设置最强约束区间
			long oldsize = feature.getsize(v);
			
			if ((size>oldsize&&flag==false)||(size<oldsize&&flag==true)) {
				feature.addVariable(v, size, despbuf.toString(), despmet.toString(), flag);
			}
			return;
		}
		
		//当前变量为参数或者外部变量，记录
		if (v.isParam() ||  bufDecl.getScope() instanceof SourceFileScope) {
			feature.addVariable(v, size, despbuf.toString(), despmet.toString(), flag);
		}
		
	}
	/**
	 * 确定当前变量是否存在BO前置约束
	 * @param bufDomain
	 * @param srcDecl
	 * @param feature
	 */
	private void confirmBOVar(long size, VariableNameDeclaration srcDecl, StringBuffer despbuf, StringBuffer despmet, MethodBOPreCondition feature,boolean flag) {
		Variable v = Variable.getVariable(srcDecl);
		if (v == null){
			//既不是参数也不是外部变量，只能是函数内部定义的局部变量//暂时只解决一维数组
				SimpleNode srcNode=srcDecl.getNode();
				ASTPrimaryExpression pNode=(ASTPrimaryExpression) srcNode.getSingleChildofType(ASTPrimaryExpression.class);
				if(pNode==null||pNode.jjtGetNumChildren()!=0)
					return ;
				else{
					VariableNameDeclaration src=pNode.getVariableDecl();
					v=Variable.getVariable(src);
					if(v==null)
						return ;
				}
		}
			
		
		if (feature.contains(srcDecl)) {//如果已经  存在，比较区间，设置最强约束区间
			long oldsize = feature.getsize(v);
			
			if ( size<oldsize&&flag==true) {
				feature.addVariable(v, size, despbuf.append("；").toString(), despmet.toString(), flag);
			}
			return;
		}
		
		//当前变量为参数或者外部变量，记录
		if (v.isParam() ||  srcDecl.getScope() instanceof SourceFileScope) {
			feature.addVariable(v, size,despbuf.append("；").toString(), despmet.toString(), flag);
		}
		
	}
	
	@Override
	/**
	 * 功能：重写抽象语法树的访问者方法，计算函数摘要
	 */
	public Object visit(ASTCompoundStatement node,Object data) {
	
		MethodBOPreCondition feature = (MethodBOPreCondition)data;
		//匹配出所有的函数结点，看是否具有bopreconditon摘要信息
		String xPath=".//PostfixExpression/PrimaryExpression[@Method='true'] ";
		
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);
		
		//创建一个区间运算访问者对象
		//chh  ExpressionValueVisitor expVisitor = new ExpressionValueVisitor();
		
		//遍历所有函数
		for(SimpleNode snode: evaluationResults) {
			//得到函数声明信息
			MethodNameDeclaration methodDecl = StateMachineUtils.getMethodNameDeclaration(snode);
			
			if(methodDecl == null) {
				continue;
			}
			
			StringBuffer despmet = new StringBuffer("它在文件第"+snode.getBeginLine()+"引用了函数"+methodDecl.getImage()+"，");
			//调用BOFunction 类型的函数也需要检查是否应该生成函数摘要（FORBIDDEN型不需要）
			if(BOFunction.isBOfunc(methodDecl)!=null){
				BOFunction bofunc=BOFunction.isBOfunc(methodDecl);
				if(bofunc.type == BOType.FORMATIN){
					SimpleNode fsArg = StateMachineUtils.getArgument(snode, bofunc.srcIndex);
					ASTConstant  strNode=null;
					//目前默认格式字符串是字符串常量
					if(fsArg.getSingleChildofType(ASTConstant.class)!=null)
						{
							strNode=(ASTConstant) fsArg.getSingleChildofType(ASTConstant.class);
							if(strNode.getImage().contains("%"))
							{
								List<Long> lenList = BOHelper.getFSVarsLenList(strNode.getImage(),false);
								
								int index = bofunc.bufIndex;
								int len = lenList.size();
								
								for (int i = 0; i < len; ++i) {
									SimpleNode argNode = StateMachineUtils.getArgument(snode, index+i);
									if(argNode==null)
									{
										continue;
									}
									SimpleNode  pNode=(SimpleNode) argNode.getSingleChildofType(ASTPrimaryExpression.class);
									VariableNameDeclaration  bufDecl=null;
									long bufsize=0;
									if(pNode!=null){
										bufDecl=pNode.getVariableNameDeclaration();
										bufsize= BOStateMachine.getbuflength(pNode);
									}
					
									long l = lenList.get(i);
									if(l==-1||bufDecl==null||(bufsize!=0&&!(bufDecl.getScope() instanceof SourceFileScope))) 
										continue;
									else 
										this.confirmBOVar( l, bufDecl,despmet ,feature,false);
									//数字会不会溢出//目前只处理字符串
								}
							}
						}
				}
				else if(bofunc.type == BOType.FORMATSTRING){
					
						SimpleNode bufArg = StateMachineUtils.getArgument(snode, bofunc.bufIndex);
						SimpleNode  pNode=(SimpleNode) bufArg.getSingleChildofType(ASTPrimaryExpression.class);
						VariableNameDeclaration  bufDecl=null;
						long bufsize=0;
						if(pNode!=null){
							bufDecl=pNode.getVariableNameDeclaration();
							bufsize= BOStateMachine.getbuflength(pNode);
						}
						SimpleNode srcArg = StateMachineUtils.getArgument(snode, bofunc.srcIndex);
						ASTConstant  srcNode=(ASTConstant) srcArg.getSingleChildofType(ASTConstant.class);
						if(srcNode==null)
							continue;
						if (bufDecl == null) {
							continue;
						}
						
						if (bofunc.limitLen != -1) {
							//得到目标缓冲区的类型，判断是否为宽字节字符
							boolean isUnicode = false;
							boolean isStringRelated = false;
							
							
							CType varType = bufDecl.getType();
							if (varType.toString().endsWith("wchar_t")) {
								isUnicode = true;
								isStringRelated = true;
							} else if (varType.toString().endsWith("char")) {
								isStringRelated = true;
							}
							
							SimpleNode limitArg = (SimpleNode) StateMachineUtils.getArgument(snode, bofunc.limitLen);
							long tmpsize=0;
							if(limitArg.jjtGetNumChildren()==1&&limitArg.jjtGetChild(0) instanceof ASTAdditiveExpression){
								limitArg=(SimpleNode) limitArg.jjtGetChild(0);
								tmpsize=BOStateMachine.getsrclength(limitArg);
							}
							else {
								limitArg=(SimpleNode) limitArg.getFirstChildInstanceofType(ASTPrimaryExpression.class);
								if(limitArg.jjtGetNumChildren()==0)
									tmpsize=BOStateMachine.getsrclength(limitArg);
								else if(limitArg.jjtGetNumChildren()==1&&limitArg.jjtGetChild(0) instanceof ASTConstant)
									tmpsize=BOStateMachine.getsrclength((SimpleNode) limitArg.getSingleChildofType(ASTConstant.class));
								else if(limitArg.jjtGetNumChildren()==1&&limitArg.jjtGetChild(0) instanceof ASTExpression){
									tmpsize=BOStateMachine.getsrclength((SimpleNode) limitArg);
								}
							}
							long limitLen = tmpsize;//getsrclength(limitArg);
							VariableNameDeclaration  limitvar=limitArg.getVariableNameDeclaration();
							if(limitvar!=null&&(bufsize!=0)
									&&(limitLen==0||limitvar.getScope() instanceof SourceFileScope)){
								if (isUnicode) {
									bufsize/= 2;
								}
								if (isStringRelated) {
									--bufsize;
								} 
								this.confirmBOVar(bufsize, limitvar,new StringBuffer("目标缓冲区："+bufDecl.getImage()), despmet, feature,true);
							}
							else if((bufsize==0||bufDecl.getScope() instanceof SourceFileScope)&&limitLen!=0&&bufDecl!=null){
								if (isStringRelated) {
									++limitLen;
								} 
								if (isUnicode) {
									limitLen *= 2;
								}
								this.confirmBOVar(limitLen, bufDecl, despmet, feature,false);
							}
						} else {
							long fssize = BOStateMachine.getFSDomain(srcNode.getImage(), snode, bofunc);
						
							if (bufsize!=0&&bufsize<fssize&&!(bufDecl.getScope() instanceof SourceFileScope)){
								continue;
							}
								
							boolean result=false;
							List<Long> lenList = BOHelper.getFSVarsLenList(srcNode.getImage(),true);
							for(int i = 0; i < lenList.size(); ++i)
							{
								SimpleNode argNode = StateMachineUtils.getArgument(snode, bofunc.srcIndex+1+i);
								if(argNode==null)
								{
									continue;
								}
								SimpleNode  srcpNode=(SimpleNode) argNode.getFirstChildInstanceofType(ASTPrimaryExpression.class);
								NameDeclaration  bufRe=null;
								if(srcNode!=null)
									bufRe=srcpNode.getVariableNameDeclaration();
								if (bufRe!=null&&bufRe instanceof VariableNameDeclaration) {
									VariableNameDeclaration varDecl = ((VariableNameDeclaration)bufRe);
									if (varDecl.getScope() instanceof SourceFileScope||varDecl.isParam()) 
										result = true;	
								}
								else if(bufRe!=null&&bufRe instanceof MethodNameDeclaration){
									result = true;
								}
								else if(bufRe==null&&argNode.getFirstChildInstanceofType(ASTConstant.class)==null){
									result = true;
								}
							}
							if(bufDecl!=null&&(bufsize==0||bufDecl.getScope() instanceof SourceFileScope)&&result==false&&fssize!=0)
								this.confirmBOVar(fssize, bufDecl, despmet, feature,false);
						}	
				}
				else 
					continue;
			}
			MethodSummary  methodSum=methodDecl.getMethodSummary();

			if(methodSum == null) {
				continue;
			}
			//判断是否有BO的函数摘要
			MethodBOPreCondition boPrecon = (MethodBOPreCondition) methodSum.findMethodFeature(MethodBOPreCondition.class);
			if(boPrecon == null) {
				continue;
			}
			//判断此函数是否是库函数，与自定义函数分开处理()
			if(methodDecl.isLib()) {
			
				if(boPrecon.getSubtype() == BOType.BUFFERCOPY) {
					
					//得到当前函数的buf参数结点，目的缓冲区的区间
					SimpleNode bufNode = StateMachineUtils.getArgument(snode, boPrecon.getBufIndex());				
					if (bufNode == null)
						continue;
					
					//modified by nmh
					SimpleNode  bufpNode = null;
					VariableNameDeclaration  bufDecl=null;
					long bufsize=0;
					ASTPostfixExpression postNode = (ASTPostfixExpression)bufNode.getSingleChildofType(ASTPostfixExpression.class);
					if(postNode!= null && ( postNode.getOperators().contains(".") || postNode.getOperators().contains("->") ))
					{
						NameDeclaration decl = null;
						decl = postNode.getVariableDecl();
						if (decl instanceof VariableNameDeclaration) {
							bufDecl = (VariableNameDeclaration) decl;
						}
						if (bufDecl == null) {
							continue;
						}
						bufsize=BOStateMachine.getbuflength(postNode);
					}
					else
					{
						bufpNode = (SimpleNode) bufNode.getSingleChildofType(ASTPrimaryExpression.class);					
						if(bufpNode!=null)
							bufDecl=bufpNode.getVariableNameDeclaration();
						if (bufDecl == null) {
							continue;
						}
						bufsize=BOStateMachine.getbuflength(bufpNode);
					}
					
					boolean isStringRelated = false; //表示目的缓冲区的类型是否为字符串相关的,包括宽字节字符
					boolean isUnicode = false;
					
					CType varType = bufDecl.getType();
					if (varType.toString().endsWith("char")) {
						isStringRelated = true;
					} else if (varType.toString().endsWith("wchar_t")) {
						isStringRelated = true;
						isUnicode = true;
					}
					
					
					int arrayTypeSize=4;  //默认为int型，4个字节
					/*bufsize为目的缓冲区的字节长度*/
					if(varType instanceof CType_AbstPointer)
					{
						CType originalArrayType = ((CType_AbstPointer) varType).getOriginaltype();
						if(originalArrayType!=null)
						{
							arrayTypeSize = originalArrayType.getSize();
						}
					}
					if(arrayTypeSize != 0 )
					   bufsize/= arrayTypeSize;
					//end
					
					SimpleNode srcNode = null;
					SimpleNode srcpNode= null;
					long srcsize=0;
					if(boPrecon.getLimitLen() != -1) {
						long tmpsize=0;
						SimpleNode priNode =null;
						srcNode = StateMachineUtils.getArgument(snode, boPrecon.getLimitLen());
						if(srcNode.jjtGetNumChildren()==1&&srcNode.jjtGetChild(0) instanceof ASTAdditiveExpression){
							srcpNode=(SimpleNode) srcNode.jjtGetChild(0);
							tmpsize=BOStateMachine.getsrclength(srcpNode);
						}
						else{
							if(srcNode != null )
							{
								priNode = (SimpleNode) srcNode.getFirstChildInstanceofType(ASTPrimaryExpression.class);
								if(priNode != null && priNode.jjtGetNumChildren()==0){
									srcpNode=priNode;
									tmpsize=BOStateMachine.getsrclength(srcpNode);
								}
								else if(priNode !=null && priNode.jjtGetNumChildren()==1&&priNode.jjtGetChild(0) instanceof ASTConstant){
									srcpNode=(SimpleNode) priNode.getSingleChildofType(ASTConstant.class);
									tmpsize=BOStateMachine.getsrclength(srcpNode);
								}
								else if(priNode !=null && priNode.jjtGetNumChildren()==1&&priNode.jjtGetChild(0) instanceof ASTExpression){
									srcpNode=(SimpleNode) priNode;
									tmpsize=BOStateMachine.getsrclength(srcpNode);
								}
							}
						}
						
						
						if (!boPrecon.isNeedNull()) { //not need to reserve one byte for '\0', such as memset.
							if (tmpsize != 0) {
								if (!isUnicode) {
									srcsize = tmpsize;
								} else { //wide characters.
									srcsize = tmpsize*2;
								}
							}
							else if(bufsize!=0){
								if (isUnicode) {
									bufsize/=2;
								} 
							}
						} else {
							if (tmpsize != 0) {
								
								if (isStringRelated) {
									++tmpsize;
								}
								
								if (isUnicode) { //it's wide characters.
									tmpsize *= 2;
								}
								
								srcsize = tmpsize;
							}
							/*else if(bufsize!=0){
								if (isUnicode) {
									bufsize/=2;
								} 
								if (isStringRelated) {
									--bufsize;
								}
							}*/
						}
					} else {
						srcNode = StateMachineUtils.getArgument(snode, boPrecon.getSrcIndex());
						if(srcNode == null)
							continue;
						ASTPostfixExpression srcpostNode = (ASTPostfixExpression)srcNode.getSingleChildofType(ASTPostfixExpression.class);
						if(srcpostNode!= null && ( srcpostNode.getOperators().contains(".") || srcpostNode.getOperators().contains("->") ))
						{
							srcsize=BOStateMachine.getsrclength(srcpostNode);//计算出源或者限制长度的区间值
						}
						else
						{
							srcpNode = (SimpleNode)srcNode.getSingleChildofType(ASTPrimaryExpression.class);
							if(srcpNode==null)
								continue;
							if (srcpNode.getSingleChildofType(ASTConstant.class)!=null) { //it's a constant string.
								String string =((ASTConstant) srcpNode.getSingleChildofType(ASTConstant.class)).getImage();
								if (string.startsWith("\"")) {
									string = string.substring(1);
								} else if (string.startsWith("L\"")) { //it's wide characters.
									string = string.substring(2);
								}

								if (string.endsWith("\"")) {
									string = string.substring(0, string.length()-1);
								}

								long length = BOHelper.getConstStrLength(string);

								if (isUnicode) { //it's wide characters.
									length *= 2;
								}

								srcsize = length;
							} else {
								srcsize=BOStateMachine.getsrclength(srcpNode);//计算出源或者限制长度的区间值
							}
						}
						
					}
					
					VariableNameDeclaration srcDecl=null ;
					if (srcNode != null){//&&!(srcpNode instanceof ASTExpression)
						srcDecl = StateMachineUtils.getVarDeclaration(srcNode);
					}
					
					if(methodDecl.getImage().startsWith("strcat")||methodDecl.getImage().startsWith("strncat")){
						
						if(bufsize!=0 && bufpNode!=null){
							bufsize-=BOStateMachine.getoldsize( (ASTPrimaryExpression) bufpNode);
						}
						if(srcsize!=0 && bufpNode!=null){
							srcsize+=BOStateMachine.getoldsize( (ASTPrimaryExpression) bufpNode);
						}
					}
					
					if(bufsize!=0&&srcDecl!=null&&(srcsize==0||srcDecl.getScope() instanceof SourceFileScope))
						this.confirmBOVar(bufsize, srcDecl,new StringBuffer("目标缓冲区："+bufDecl.getImage()), despmet, feature, true);
					else if((bufsize==0||bufDecl.getScope() instanceof SourceFileScope)&&srcsize!=0&&bufDecl!=null)
						this.confirmBOVar(srcsize, bufDecl, despmet, feature, false);
					methodDecl.getMethod().setMtSummmary(methodSum);
				}
			} else {
			//该函数为用户自定义的函数，处理前置条件的传播
				Set<Variable> varList = boPrecon.getBOVariables();
				
				for(Variable var: varList) {
					despmet = despmet.append( boPrecon.getDespmet(var));
					if(boPrecon.getflag(var)==true){
						if (var.isParam() || var.getScopeType() == ScopeType.INTER_SCOPE) {	
							long bufsize = boPrecon.getsize(var);
							VariableNameDeclaration srcDecl = null;
							if(var.getParamIndex() == -1)//如果是全局变量调用
							{
								NameDeclaration nd=Search.searchInVariableUpward(var.getName(),snode.getScope());
								if(nd instanceof VariableNameDeclaration)
									srcDecl = (VariableNameDeclaration)nd;
							}
							else
							{
								SimpleNode argNode = StateMachineUtils.getArgument(snode, var.getParamIndex());
								srcDecl = StateMachineUtils.getVarDeclaration(argNode);
							}
								
							if (srcDecl == null||(!srcDecl.isParam()&&!(srcDecl.getScope() instanceof SourceFileScope)))
								continue;
							this.confirmBOVar(bufsize, srcDecl, new StringBuffer(boPrecon.getDespbuf(var)),despmet, feature,true);
						}
					}
					else{
						if (var.isParam()) {
							
							long srcsize = boPrecon.getsize(var);
							SimpleNode argNode = StateMachineUtils.getArgument(snode, var.getParamIndex());
							VariableNameDeclaration bufDecl = StateMachineUtils.getVarDeclaration(argNode);
							if (bufDecl == null||(!bufDecl.isParam()&&!(bufDecl.getScope() instanceof SourceFileScope)))
								continue;
							this.confirmBOVar(srcsize, bufDecl, despmet, feature,false);
						}
					}
				}
			}
		}
		return null;
	}

}


