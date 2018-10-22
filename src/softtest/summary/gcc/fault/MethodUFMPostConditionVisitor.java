package softtest.summary.gcc.fault;

import java.util.ArrayList;
import java.util.List;

import softtest.ast.c.ASTArgumentExpressionList;
import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.CParserVisitorAdapter;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.VexNode;
import softtest.config.c.Config;
import softtest.domain.c.analysis.ExpressionValueVisitor;
import softtest.domain.c.analysis.ExpressionVistorData;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.DomainType;
import softtest.domain.c.interval.PointerDomain;
import softtest.domain.c.interval.PointerValue;
import softtest.domain.c.symbolic.Expression;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.Variable;
import softtest.summary.c.MethodFeature;
import softtest.summary.c.MethodFeatureVisitor;
import softtest.summary.c.MethodSummary;
import softtest.symboltable.c.ClassScope;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.SourceFileScope;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.Type.CType_Pointer;

public class MethodUFMPostConditionVisitor extends CParserVisitorAdapter implements MethodFeatureVisitor {

	private static MethodUFMPostConditionVisitor instance;
	
	/**
	 * 摘要访问者当前所在的函数对应的函数声明 
	 */
	private MethodNameDeclaration methodDecl;
	
	private MethodUFMPostConditionVisitor() {
	}
	
	public static MethodUFMPostConditionVisitor getInstance() {
		if(instance == null) {
			instance = new MethodUFMPostConditionVisitor();
		}
		return instance;
	}
	
	/**
	 * 函数控制流out结点计算摘要，vexnode一般为func_out
	 */
	public void visit(VexNode vexNode) {
		if (vexNode.getTreenode() == null) {
			return;
		}
		MethodUFMPostCondition feature = new MethodUFMPostCondition();
		
		//这里控制流结点对应的语法树节点一般为function_definition
		SimpleNode node = vexNode.getTreenode();
		if (node == null) {
			return;
		}
		methodDecl = InterContext.getMethodDecl(vexNode);
		if (methodDecl != null) {
			node.jjtAccept(this, feature);
		}
		if (feature.isEmpty()) {
			return;
		}
		
		MethodSummary summary = InterContext.getMethodSummary(vexNode);
		if (summary != null) {
			summary.addPostCondition(feature);
			if (Config.INTER_METHOD_TRACE) {
				if (methodDecl != null) {
					System.err.println(methodDecl.getFullName() + " " + feature);
				}
			}
		}
	}

	@Override
	public Object visit(ASTAssignmentExpression node, Object data) {
		MethodUFMPostCondition feature = (MethodUFMPostCondition) data;
		//检查是否对全局或者类成员指针变量重新赋值
		String oper = node.getOperators();
		if(oper.equals("=")) {		//形如 p = xxx的赋值语句
			if(node.jjtGetNumChildren() == 3
					&& node.jjtGetChild(2) instanceof ASTAssignmentExpression) {
				ExpressionValueVisitor exp = new ExpressionValueVisitor();
				ExpressionVistorData domaindata = new ExpressionVistorData();
				Object re  = node.getVariableNameDeclaration();
				exp.visit((SimpleNode)node.jjtGetChild(0), domaindata);
				if(re instanceof VariableNameDeclaration) {
					Variable variable = Variable.getVariable((VariableNameDeclaration)re);
					if(variable != null) {
						feature.removeVariable(variable);	//若当前后置信息中有此变量，则删除
					}
				}
			}
		}
		return super.visit(node, data);
	}

//	@Override
//	public Object visit(ASTdelete_expression node, Object data) {
//		MethodUFMPostCondition feature = (MethodUFMPostCondition) data;
//		if(node.jjtGetNumChildren() == 1 && node.jjtGetChild(0) instanceof ASTunary_expression) {
//			//获取指针变量
//			ExpressionValueVisitor exp = new ExpressionValueVisitor();
//			ExpressionVistorData domaindata = new ExpressionVistorData();
//			Object re  = node.getVariableNameDeclaration();
//			exp.visit((SimpleNode)node.jjtGetChild(0), domaindata);
//			if(isUFMPostVar(domainData, re, node, feature)) {
//				Variable variable = Variable.getVariable((VariableNameDeclaration)re);
//				if(variable != null) {
//					feature.addVariable(variable, "在文件" + node.getFileName() + "中函数"  + methodDecl.getName() + "第" + node.getBeginLine() + "行处被释放");
//				}
//			}
//		}
//		return super.visit(node, data);
//	}

	@Override
	public Object visit(ASTPrimaryExpression node, Object data) {
		MethodUFMPostCondition feature = (MethodUFMPostCondition)data;
		if(node.isMethod() && node.getMethodDecl() != null) {
			MethodNameDeclaration methodDecl = (MethodNameDeclaration) node.getMethodDecl();
			MethodSummary mtSummary = methodDecl.getMethodSummary();
			if (node.isMethod() && methodDecl.getImage().equals("free")) {
				// 系统库函数，free(p)
				List funcNode = ((SimpleNode)node.jjtGetParent()).findChildrenOfType(ASTArgumentExpressionList.class);
				if (funcNode.size() == 0) {
					return null;
				}
				ASTArgumentExpressionList decNode = (ASTArgumentExpressionList) funcNode.get(0);
				if (decNode.jjtGetNumChildren() != 1) {
					return null;
				}
				List paramsNode = decNode.findChildrenOfType(ASTUnaryExpression.class);
				if (paramsNode.size() == 0) {
					return null;
				}
				ASTUnaryExpression paramNode = (ASTUnaryExpression) paramsNode.get(0);
				ExpressionValueVisitor exp = new ExpressionValueVisitor();
				ExpressionVistorData domaindata = new ExpressionVistorData();
				domaindata.currentvex = node.getCurrentVexNode();
				Object re = paramNode.getVariableDecl();
				exp.visit((SimpleNode) paramNode, domaindata);

				Expression value1 = domaindata.value;
				Domain mydomain = null;
				if (value1 != null)
					mydomain = value1.getDomain(domaindata.currentvex
							.getSymDomainset());
				if (isUFMPostVar(mydomain, re, node, feature)) {
					Variable variable = Variable
							.getVariable((VariableNameDeclaration) re);
					if (variable != null) {
						feature.addVariable(variable, "在文件"
								+ node.getFileName() + "中函数"
								+ this.methodDecl.getImage() + "第"
								+ node.getBeginLine() + "行处被释放");
					}
				}
			} else {
				if (mtSummary != null) {
					for (MethodFeature postFeature : mtSummary
							.getPostConditions()) {
						if (postFeature instanceof MethodUFMPostCondition) { // 此函数的UFM后置信息
							MethodUFMPostCondition postUFMCondition = (MethodUFMPostCondition) postFeature; // 此函数的UFM后置信息
							for (Variable variable : postUFMCondition
									.getUFMVariables()) {
								if (feature.contains(variable)) { // 若当前函数已有此变量后置信息，不再记录
									continue;
								}
								ArrayList<String> desp = postUFMCondition
										.getDesp(variable); // 此变量的当前后置信息描述
								// 连接两个描述
								desp.add("在文件" + node.getFileName() + "中函数"
										+ this.methodDecl.getImage() + "第"
										+ node.getBeginLine() + "行处");
								feature.addVariable(variable, desp);
							}
						}
					}
				}
			}
		}
		return null;
	}

//	@Override
//	public Object visit(ASTqualified_id node, Object data) {
//		MethodUFMPostCondition feature = (MethodUFMPostCondition)data;
//		//可能的函数调用结点，一种是free(p)，检测p是否为满足后置条件的变量；另一种则是后置信息的传递
//		if(node.isMethod() && node.getNameDeclaration() != null) {
//			MethodNameDeclaration methodDecl = (MethodNameDeclaration) node.getNameDeclaration();
//			if(methodDecl.isLib() && methodDecl.getName().equals("free")) {
//				//系统库函数，free(p)
//				List funcNode = node.getParentsOfType(ASTdeclaration.class);
//				if (funcNode.size() == 0) {
//					return null;
//				}
//				ASTdeclaration decNode = (ASTdeclaration)funcNode.get(0);
//				if (decNode.jjtGetNumChildren() != 2) {
//					return null;
//				}
//				ExpressionValueVisitor exp = new ExpressionValueVisitor();
//				ExpressionVistorData domaindata = new ExpressionVistorData();
//				Object re  = node.getVariableNameDeclaration();
//				exp.visit((SimpleNode)node.jjtGetChild(0), domaindata);
//				if(isUFMPostVar(domainData, re, node, feature)) {
//					Variable variable = Variable.getVariable((VariableNameDeclaration)re);
//					if(variable != null) {
//						feature.addVariable(variable, "在文件" + node.getFileName() + "中函数"  + this.methodDecl.getName() + "第" + node.getBeginLine() + "行处被释放");
//					}
//				}
//			} else {
//				if(methodDecl.isLib()) {
//					return null;
//				}
//				//用户自定义函数
//				MethodSummary mtSummary = methodDecl.getMethodSummary();
//				if(mtSummary != null) {
//					for(MethodFeature postFeature : mtSummary.getPostConditions()) {
//						if(postFeature instanceof MethodUFMPostCondition) {		//此函数的UFM后置信息
//							MethodUFMPostCondition postUFMCondition = (MethodUFMPostCondition) postFeature;		//此函数的UFM后置信息
//							for(Variable variable : postUFMCondition.getUFMVariables()) {
//								if(feature.contains(variable)) {				//若当前函数已有此变量后置信息，不再记录
//									continue;
//								}
//								ArrayList<String> desp = postUFMCondition.getDesp(variable);	//此变量的当前后置信息描述
//									//连接两个描述
//								desp.add("在文件" + node.getFileName() + "中函数"  + this.methodDecl.getImage() + "第" + node.getBeginLine() + "行处");
//								feature.addVariable(variable, desp);
//							}
//						}
//					}
//				}
//			}
//		}
//		return null;
//	}
	
	/**
	 *	检测obj是否为满足后置条件的指针变量 
	 */
	private boolean isUFMPostVar(Domain domaindata, Object obj, SimpleNode node, MethodUFMPostCondition feature) {
		if(!(obj instanceof VariableNameDeclaration)) {		//是否为变量
			return false;
		}
		VariableNameDeclaration var = (VariableNameDeclaration) obj;
		if(feature.contains(var)) {							
			return false;
		}
		if(!(var.getType() instanceof CType_Pointer)) {	//是否为指针类型
			return false;
		}
		if(!(var.getScope() instanceof ClassScope || var.getScope() instanceof SourceFileScope)) {		//是否为全局或者类成员变量
			return false;
		}
		if(domaindata != null && domaindata instanceof PointerDomain) {
			PointerDomain pd = (PointerDomain) domaindata;
			if(pd.getDomaintype() != DomainType.UNKNOWN && pd.getValue() != PointerValue.NULL) {			//区间是否为空
				return false;								
			}
		}
		VexNode vex = node.getCurrentVexNode();
		if(vex == null || vex.getContradict()) {			//是否处于不可达路径
			return false;
		}
		return true;
	}
	
}
