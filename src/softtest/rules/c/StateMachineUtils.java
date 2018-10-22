package softtest.rules.c;

import java.util.List;

import org.jaxen.BaseXPath;
import org.jaxen.JaxenException;
import org.jaxen.XPath;

import softtest.ast.c.*;
import softtest.tools.c.jaxen.DocumentNavigator;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.NameDeclaration;
import softtest.symboltable.c.VariableNameDeclaration;

public class StateMachineUtils {

	public static List<SimpleNode> getEvaluationResults(SimpleNode node, String xPath) {
		List<SimpleNode> evaluationResults = null;
		try {
			XPath xpath = new BaseXPath(xPath, new DocumentNavigator());
			evaluationResults = xpath.selectNodes(node);
		} catch (JaxenException e) {
			e.printStackTrace();
			throw new RuntimeException("xpath error");
		}
		return evaluationResults;
	}
	
	public static MethodNameDeclaration getMethodDefinition(SimpleNode node) {
		if (node instanceof ASTFunctionDefinition) {
			return ((ASTFunctionDefinition)node).getDecl();
		} 
		return null;
	}
	
	public static MethodNameDeclaration getMethodNameDeclaration(SimpleNode snode) {
		AbstractExpression funcNode = (AbstractExpression)snode;
		if (!funcNode.isMethod()) {
			return null;
		}
		MethodNameDeclaration methodDecl = null;
		if (snode instanceof ASTPrimaryExpression) {
			methodDecl = (MethodNameDeclaration)((ASTPrimaryExpression)funcNode).getMethodDecl();
		} 
		return methodDecl;
	}
	
	public static VariableNameDeclaration getVarDeclaration(SimpleNode snode) {
		if (snode == null) {
			return null;
		}
		if (snode instanceof ASTDirectDeclarator) {
			return (VariableNameDeclaration)((ASTDirectDeclarator)snode).getDecl();
		}
		AbstractExpression funcNode = (AbstractExpression)snode;
		if (funcNode.isMethod()) {
			return null;
		}
		List<SimpleNode> temp = StateMachineUtils.getEvaluationResults(snode, ".//PrimaryExpression");
		if (temp == null || temp.size() == 0) {
			return null;
		}
		
		VariableNameDeclaration varDecl = null;
		NameDeclaration tmpDecl = null;
		
		if (temp.get(0) instanceof ASTPrimaryExpression) 
		{
			tmpDecl = ((ASTPrimaryExpression)temp.get(0)).getVariableDecl();
			if (tmpDecl instanceof VariableNameDeclaration)
				varDecl = (VariableNameDeclaration)tmpDecl;
		} 
		else if (temp.get(0) instanceof ASTDirectDeclarator) 
		{
			tmpDecl = ((ASTDirectDeclarator)temp.get(0)).getDecl();
			if (tmpDecl instanceof VariableNameDeclaration)
				varDecl = (VariableNameDeclaration)tmpDecl;
		}
	
		return varDecl;
	}
	//new
	public static SimpleNode getArgumentsNode(SimpleNode node) {
		if (node instanceof ASTDirectDeclarator&&((ASTDirectDeclarator)node).isFunctionName()) {
			ASTDirectDeclarator qid = (ASTDirectDeclarator)node;
			return qid.getArgumnetNode();
			
		} else if (node instanceof ASTPrimaryExpression) {
			ASTPrimaryExpression id = (ASTPrimaryExpression)node;
			return (SimpleNode)id.getArgumnetNode();
		}
		return null;
	}
	
	/*public static SimpleNode getArgument(SimpleNode node, int index) {
		if (node instanceof ASTqualified_id && index == 0) {
			ASTqualified_id qid = (ASTqualified_id)node;
			return qid.getArgumnetNode();
		} else if (node instanceof ASTid_expression) {
			ASTid_expression id = (ASTid_expression)node;
			if (id.getArgumnetNode() != null && id.getArgumnetNode().jjtGetNumChildren() >= index) {
				return (SimpleNode)id.getArgumnetNode().jjtGetChild(index);
			}
		}
		return null;
	}*/
	
	//modified 
	public static SimpleNode getArgument(SimpleNode node, int index) {
		 if (node instanceof ASTPrimaryExpression&&((ASTPrimaryExpression)node).isMethod()) {
			ASTPrimaryExpression id = (ASTPrimaryExpression)node;
			ASTPostfixExpression po = (ASTPostfixExpression)id.jjtGetParent();
			if (po!=null&&po.jjtGetNumChildren()==2 && po.jjtGetChild(1)instanceof ASTArgumentExpressionList) {
				if(po.jjtGetChild(1).jjtGetNumChildren() > index)
				return (SimpleNode)po.jjtGetChild(1).jjtGetChild(index);
			} else {
				return getDefaultValueArg(node, index);
			}
		}
		return null;
	}
	
	public static ASTPrimaryExpression getArgumentnew(SimpleNode func,
			int paramIndex) {
		if (func == null) {
			return null;
		}
		String xPath = ".//ArgumentExpressionList/AssignmentExpression["
				+ paramIndex
				+ "]//UnaryExpression/PostfixExpression/PrimaryExpression[not (./Expression)]";
		List params = getEvaluationResults(func, xPath);
		if (params.size() >= 1) {
			return (ASTPrimaryExpression) params.get(0);
		}
		return null;
	}
	
	
	/**
	 * 获得函数声明中index位置的参数结点，从0开始 
	 */
	public static SimpleNode getDefaultValueArg(SimpleNode node, int index) {
		NameDeclaration nameDecl = null;
		if (node instanceof ASTPrimaryExpression&&((ASTPrimaryExpression)node).isMethod()) {
			nameDecl = ((ASTPrimaryExpression)node).getMethodDecl();
		}
		if(nameDecl == null  ) {
			return null;
		}
		MethodNameDeclaration methodDecl = (MethodNameDeclaration) nameDecl;
		SimpleNode funcNode = methodDecl.getNode();
		if(funcNode == null) {
			return null;
		}
		List list = funcNode.findChildrenOfType(ASTParameterList.class);
		if(list.size() == 0) {
			return null;
		}
		ASTParameterList paramList = (ASTParameterList) list.get(0);
		if(index >= paramList.jjtGetNumChildren()) {
			return null;
		}
		return (SimpleNode) paramList.jjtGetChild(index);
	}
}
