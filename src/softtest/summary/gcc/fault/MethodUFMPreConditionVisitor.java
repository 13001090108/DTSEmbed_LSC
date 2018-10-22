package softtest.summary.gcc.fault;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import softtest.ast.c.ASTArgumentExpressionList;
import softtest.ast.c.ASTPostfixExpression;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.ASTUnaryOperator;
import softtest.ast.c.CParserVisitorAdapter;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.VexNode;
import softtest.config.c.Config;
import softtest.domain.c.analysis.ExpressionValueVisitor;
import softtest.domain.c.analysis.ExpressionVistorData;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.DomainType;
import softtest.domain.c.interval.PointerDomain;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.Variable;
import softtest.summary.c.MethodFeature;
import softtest.summary.c.MethodFeatureVisitor;
import softtest.summary.c.MethodSummary;
import softtest.symboltable.c.ClassScope;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.NameOccurrence;
import softtest.symboltable.c.SourceFileScope;
import softtest.symboltable.c.VariableNameDeclaration;

public class MethodUFMPreConditionVisitor extends CParserVisitorAdapter implements MethodFeatureVisitor {

	private static MethodUFMPreConditionVisitor instance;
	
	private MethodNameDeclaration methodDecl;
	
	private MethodUFMPreConditionVisitor() {
	}
	
	public static MethodUFMPreConditionVisitor getInstance() {
		if(instance == null) {
			instance = new MethodUFMPreConditionVisitor();
		}
		return instance;
	}

	public void visit(VexNode vexNode) {
		if (vexNode.getTreenode() == null) {
			return;
		}
		MethodUFMPreCondition feature = new MethodUFMPreCondition();
		
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
			summary.addPreCondition(feature);
			if (Config.INTER_METHOD_TRACE) {
				if (methodDecl != null) {
					System.err.println(methodDecl.getFullName() + " " + feature);
				}
			}
		}
	}
	
	/**
	 * 处理对指针的操作取值形如，*a
	 */
	@Override
	public Object visit(ASTUnaryExpression node, Object data) {
		MethodUFMPreCondition feature = (MethodUFMPreCondition)data;
		
		if (node.jjtGetNumChildren() != 2) {
			return super.visit(node, data);
		}
		if (!(node.jjtGetChild(0) instanceof ASTUnaryOperator) || !((ASTUnaryOperator) node.jjtGetChild(0)).getOperators().equals("*")) {
			return super.visit(node, data);
		}
		
		// 获取指针变量
		ExpressionValueVisitor exp = new ExpressionValueVisitor();
		ExpressionVistorData domaindata = new ExpressionVistorData();
		domaindata.currentvex = node.getCurrentVexNode();
		ASTUnaryExpression u = (ASTUnaryExpression) (SimpleNode)node.getFirstChildOfType(ASTUnaryExpression.class);
		VariableNameDeclaration re = null;
		if(u != null)
		  re = u.getVariableDecl();
		exp.visit((SimpleNode)node, domaindata);
		if (re== null) {
			return super.visit(node, data);
		}
		Domain domain = domaindata.currentvex.getDomain((VariableNameDeclaration) re);
		if (re != null && !isUFMVar(domain, re, node, feature)) {
			return super.visit(node, data);
		}
		Variable variable = Variable.getVariable((VariableNameDeclaration)re);
		if (variable != null) {
			feature.addVariable(variable, "在文件" + node.getFileName() + "中函数"  + methodDecl.getImage() + "第" + node.getBeginLine() + "行处");
		}
		return super.visit(node, data);
	}
	
	/**
	 * 处理对结构体指针的取成员的操作以及指针按数组取下标形如，a->b, a[1]
	 */
	@Override
	public Object visit(ASTPostfixExpression node, Object data) {
		if (node.jjtGetNumChildren() <= 1) {
			return super.visit(node, data);
		}
		
		MethodUFMPreCondition feature = (MethodUFMPreCondition)data;
		// 判断是否是[], ->操作
		ArrayList<String> operators = node.getOperatorType();
		if (operators.size() != 0) {
			if (!operators.get(0).equals("[") && !operators.get(0).equals("->")) {
				return super.visit(node, data);
			}
			// 获取指针变量
			ExpressionValueVisitor exp = new ExpressionValueVisitor();
			ExpressionVistorData domaindata = new ExpressionVistorData();
			domaindata.currentvex = node.getCurrentVexNode();
			Object re  = ((SimpleNode)node.jjtGetChild(0)).getVariableNameDeclaration();
			exp.visit((SimpleNode)node, domaindata);
			if (re== null) {
				return super.visit(node, data);
			}
			Domain domain = domaindata.currentvex.getDomain((VariableNameDeclaration) re);
			if (re != null && !isUFMVar(domain, re, node, feature)) {
				return super.visit(node, data);
			}
			
			Variable variable = Variable.getVariable((VariableNameDeclaration)re);
			if (variable != null) {
			    feature.addVariable(variable, "在文件" + node.getFileName() + "中函数"  + methodDecl.getImage() + "第" + node.getBeginLine() + "行处");
			}
			return super.visit(node, data);
		}
		return super.visit(node, data);
	}
	
	/**
	 * 处理函数调用过程中，被调用函数可能要检查的UFM前置条件
	 */
	@Override
	public Object visit(ASTPrimaryExpression node, Object data) {
		MethodUFMPreCondition feature = (MethodUFMPreCondition)data;
		if (node.isMethod() && node.getMethodDecl() != null) {
			// 被调用函数可能对实参有UFM的前置约束
			
			Set<Variable> argVars = new HashSet<Variable>();	//可能存在UFM约束的实参
			MethodNameDeclaration methodDecl = (MethodNameDeclaration)node.getMethodDecl();
			MethodUFMPreCondition subUFMPreCond = null;
			// 检查被调用函数中是否有对形参的UFM前置约束
			if (methodDecl.getMethodSummary() != null) {
				Set<MethodFeature> npdPreConds = methodDecl.getMethodSummary().getPreConditions();
				Set<Variable> vars = null;
				for (MethodFeature temp : npdPreConds) {
					if (temp instanceof MethodUFMPreCondition) {
						subUFMPreCond = (MethodUFMPreCondition)temp;
						vars = subUFMPreCond.getUFMVariables();
						break;
					}
				}
				if (vars != null) {
					for (Variable var : vars) {
//						if (var.isParam()) {
							argVars.add(var);
//						}
					}
				}
			}
			
			// 检查函数调用处，传递的参数是否跟形参的要求一致，一致的话，连接两个UFM约束
			List<SimpleNode> argNodes = getArgsNode(node);
			for (Variable var : argVars) {
				if (argNodes.size() != 0) {     // 实参
				    if (var.getParamIndex() >= argNodes.size() || var.getParamIndex() == -1) {
				        break;
				    }
					ExpressionValueVisitor exp = new ExpressionValueVisitor();
					ExpressionVistorData domaindata = new ExpressionVistorData();
					domaindata.currentvex = node.getCurrentVexNode();
					Object re  = getArgsNode(node).get(var.getParamIndex()).getVariableNameDeclaration();
					exp.visit((SimpleNode)node, domaindata);
				    
					if (re == null) {
						continue;
					}
					Domain domain = domaindata.currentvex.getDomain((VariableNameDeclaration) re);
				    if (!isUFMVar(domain, re, node, feature)) {
				        return null;
				    }
				    
				    ArrayList<String> des = subUFMPreCond.getDesp(var);
				    if (methodDecl.isLib()) {
				        des = new ArrayList<String>();
				    }
				    des.add("在文件" + node.getFileName() + "中函数"  + this.methodDecl.getImage() + "第" + node.getBeginLine() + "行处");
				    Variable variable = Variable.getVariable((VariableNameDeclaration)re);
				    if (variable != null) {
				        feature.addVariable(variable, des);
				    }
				} else {                        // 全局 类成员
                    ArrayList<String> des = subUFMPreCond.getDesp(var);
                    if (methodDecl.isLib()) {
                        des = new ArrayList<String>();
                    }
                    des.add("在文件" + node.getFileName() + "中函数"  + this.methodDecl.getImage() + "第" + node.getBeginLine() + "行处");
                    feature.addVariable(var, des);
                }
			}
		}
		return super.visit(node, data);
	}

	
	/**
	 * 判断某个变量是否符合对应的UFM前置条件
	 */
	private boolean isUFMVar(Domain domaindata, Object obj, SimpleNode node, MethodUFMPreCondition feature) {
		if (!(obj instanceof VariableNameDeclaration)) {
			return false;
		}
		
		VariableNameDeclaration var = (VariableNameDeclaration)obj;
		if (feature.contains(var)) {
			return false;
		}

		// 确认该变量类型是指针，且是参数变量或者成员变量、全局变量
		//zys：类型信息有可能为空？？暂时这么改吧
		if (var.getType()==null || !var.getType().isPointType()) {
			return false;
		}
		
		// 如果指针在此地已经是非空值则，不做前置约束
		if (domaindata != null && domaindata instanceof PointerDomain) {
			PointerDomain pDomain = (PointerDomain)domaindata;
			if (pDomain.getDomaintype() != DomainType.UNKNOWN && !pDomain.offsetRange.contains(0)) {
				return false;
			}
		}
		// 判断是否为成员、全局变量或函数参数变量,xwt于2012/11/21注释
//		if (!var.isParam() && !(var.getScope() instanceof ClassScope || var.getScope() instanceof SourceFileScope)){
//			return false;
//		}
		
		// 判断该变量之前有没有被重新赋值
		VexNode vex = node.getCurrentVexNode();
		if (vex == null || vex.getContradict()) {
			return false;							//若确定处于不可达路径上，则不记录摘要
		}
		for(NameOccurrence occ:vex.getOccurrences()){
			if(occ.getDeclaration()== var){
				List<NameOccurrence> occs = occ.getUse_def();
				if(occs!=null && !occs.isEmpty()){
					if (occs.size() == 1 && occs.get(0).getDeclaration() instanceof VariableNameDeclaration) {
						VariableNameDeclaration decl = (VariableNameDeclaration)occs.get(0).getDeclaration();
						if (decl.isParam()) {		//若被另一个参数赋值，则需要记录摘要
							return true;
						}
					}
					return false;					//被其他地址赋值，被重新分配空间，不记录摘要
				}
			}
		}
		return true;
	}

	/**
	 * 获取当前语法树节点孩子中的所有实参节点
	 */
	private List<SimpleNode> getArgsNode(ASTPrimaryExpression node) {
		List<SimpleNode> argNodes = new ArrayList<SimpleNode>();
		ASTPrimaryExpression primary = null;
		ASTPostfixExpression postfix = null;
		if (node.jjtGetParent() instanceof ASTPrimaryExpression) {
			primary = (ASTPrimaryExpression) node.jjtGetParent();
			postfix = (ASTPostfixExpression) node.jjtGetParent().jjtGetParent();
		} else if (node.jjtGetParent() instanceof ASTPostfixExpression) {
			postfix = (ASTPostfixExpression) node.jjtGetParent();
			if (postfix.jjtGetNumChildren() > 1
					&& postfix.jjtGetChild(0) instanceof ASTPrimaryExpression) {
				primary = (ASTPrimaryExpression) postfix.jjtGetChild(0);
			}
		}
		ASTArgumentExpressionList args = null;
		if (primary != null && postfix != null) {
			for (int i = 0; i < postfix.jjtGetNumChildren(); i++) {
				if (postfix.jjtGetChild(i) == primary && i + 1 < postfix.jjtGetNumChildren() && 
						postfix.jjtGetChild(i+1) instanceof ASTArgumentExpressionList) {
					args = (ASTArgumentExpressionList)postfix.jjtGetChild(i + 1);
				}
			}
		}
		if (args == null) {
			return argNodes;
		}
		for (int i = 0; i < args.jjtGetNumChildren(); i++) {
			argNodes.add((SimpleNode)args.jjtGetChild(i));
		}
		return argNodes;
	}
	
}
