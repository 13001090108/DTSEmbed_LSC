package softtest.interpro.c;

import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsmanalysis.c.AnalysisElement;
import softtest.fsmanalysis.c.CAnalysis;
import softtest.symboltable.c.*;
import softtest.symboltable.c.Type.CType_Function;

public class InterMethodVisitor extends CParserVisitorAdapter {
	
	/**
	 * 当前分析上下文中抽象语法树所在的函数节点处
	 */
	private MethodNode currMethod = null;
	
	/**
	 * 分析抽象语法树中普通函数的声明节点，建立对应的函数信息节点
	 */
	@Override
	public Object visit(ASTFunctionDefinition node, Object data) {
		MethodNameDeclaration methodDecl = node.getDecl();
		if(methodDecl.isLib())
			return data;
		Method method = getMethod(methodDecl);
		//zys:2010.8.9	如果是#include方式引入，预先生成了method，则在此更新其文件名
		//，以生成正确的文件调用关系（.h文件不会生成文件调用关系）
		if(method.getFileName().matches(InterContext.INCFILE_POSTFIX)){
			method.setFileName(methodDecl.getFileName());
		}
		AnalysisElement element = (AnalysisElement)data;
		MethodNode mtNode = null;
		if(Config.ANALYSIS_I){
			method.setFileName( method.getFileName().replace("\\", "/") );
		}
		
		if(element!=null && method.getFileName().equals(element.getFileName()))
		{
			mtNode=new MethodNode(element, method);
		}else{
			if(method.getFileName().equals("unknown"))
				mtNode=new MethodNode(CAnalysis.getElement(element.getFileName()), method);
			else
				mtNode=new MethodNode(CAnalysis.getElement(method.getFileName()), method);
		}
		mtNode = InterCallGraph.getInstance().addMethodNode(mtNode);
		methodDecl.setMethod(mtNode.getMethod());
		MethodNode old = currMethod;
		currMethod = mtNode;
		super.visit(node, data);
		currMethod = old;
		return data;
	}
	
	/**为函数声明节点也生成相关信息 */
//	public Object visit(ASTFunctionDeclaration node, Object data)
//	{
//		MethodNameDeclaration methodDecl = node.getDecl();
//		if(methodDecl==null)
//			return null;
//		Method method = getMethod(methodDecl);
//		AnalysisElement element = (AnalysisElement)data;
//		MethodNode mtNode = null;
//		if(element!=null && method.getFileName().equals(element.getFileName()))
//		{
//			mtNode=new MethodNode(element, method);
//		}else{
//			mtNode=new MethodNode(new AnalysisElement(method.getFileName()), method);
//		}
//		mtNode = InterCallGraph.getInstance().addMethodNode(mtNode);
//		methodDecl.setMethod(mtNode.getMethod());
//		
//		return null;
//	}
	
	/**
	 * zys:检测当前节点是否为函数调用,函数调用的方式目前有三种：
	 * 直接调用：f();
	 * 函数指针调用：void (*p)();		p=&f;		p();
	 * 另外一种函数指针调用：void (*p)();		p=&f;		（*p）();
	 */
	public Object visit(ASTPrimaryExpression node,Object data) 
	{
		//只有函数体内部的PrimaryExpr节点需要访问
		if(node.getScope().getEnclosingMethodScope()==null || !node.isMethod())
			return super.visit(node, data);
		//zys:暂时不处理函数指针	2010.4.8
		MethodNameDeclaration mnd=null;
		if(node.getType() instanceof CType_Function)
		{
			mnd=node.getMethodDecl();
		}
		
		if(mnd!=null && !(mnd.getNode() instanceof ASTNestedFunctionDefinition))
		{
			if(mnd.getMethodNameDeclaratorNode()==null)
			{
				if(mnd.isLib())
					return super.visit(node, data);
				//如果是用户自定义头文件中的函数声明
				if(mnd.getFileName().matches(InterContext.INCFILE_POSTFIX))
				{
					Method method=getMethod(mnd);
					MethodNode mtNode = InterCallGraph.getInstance().findMethodNode(method.getFileName(), method);
					if(mtNode.getElement()==null){
						mtNode.updateElement(CAnalysis.getElement(method.getFileName()));
					}
					if(currMethod != null){
						currMethod.addCall(mtNode);
					}
					mnd.setMethod(mtNode.getMethod());
				}else{
					//如果是extern声明的外部函数
					Method method=mnd.getMethod();
					if(method==null)
					{
						method=new Method("unknown",mnd.getImage(), mnd.getParams(), 
								((CType_Function)mnd.getType()).getReturntype(), mnd.hasVarArg());
					}
							
					MethodNode mtNode = InterCallGraph.getInstance().findMethodNode(method.getFileName(), method);
					if(currMethod != null){
						currMethod.addCall(mtNode);
					}					
					mnd.setMethod(mtNode.getMethod());
				}
			}else
			{
				Method method = getMethod(mnd);
				MethodNode mtNode = InterCallGraph.getInstance().findMethodNode(mnd.getFileName(), method);
				if(currMethod != null){
					currMethod.addCall(mtNode);
				}
				mnd.setMethod(mtNode.getMethod());
			}
		}
		return super.visit(node, data);
	}

	/**
	 * 根据函数声明信息，生成函数类型信息
	 * 
	 * @param methodDecl 函数声明信息
	 * @return 函数类型信息
	 */
	public static Method getMethod(MethodNameDeclaration methodDecl) {
		if (methodDecl.getMethod() != null) {
			return methodDecl.getMethod();
		}
		Method method = new Method(methodDecl.getFileName(),methodDecl.getImage(), methodDecl.getParams(), 
				((CType_Function)methodDecl.getType()).getReturntype(), methodDecl.hasVarArg());
		return method;
	}
}
