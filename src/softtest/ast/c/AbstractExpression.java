package softtest.ast.c;

import java.util.ArrayList;

import softtest.symboltable.c.Type.CType;
/**所有表达式语句节点的抽象基类，提供类型信息接口支持，当前可能的具体表达式节点包括；
 * ASTAdditiveExpression
 * ASTANDExpression
 * ASTArgumentExpressionList
 * ASTAssignmentExpression
 * ASTCastExpression
 * ASTConditionalExpression
 * ASTConstant
 * ASTConstantExpression
 * ASTEqualityExpression
 * ASTExclusiveORExpression
 * ASTExpression
 * ASTFieldId
 * ASTInclusiveORExpression
 * ASTLogicalANDExpression
 * ASTLogicalORExpression
 * ASTMultiplicativeExpression
 * ASTPostfixExpression
 * ASTPrimaryExpression
 * ASTRelationalExpression
 * ASTShiftExpression
 * ASTUnaryExpression
 * */
public abstract class AbstractExpression extends SimpleNode {
	CType type = null;
	/**
	 * 该节点是否是函数调用节点
	 */
	protected boolean isMethod;
	
	public AbstractExpression(CParser p, int i) {
		super(p, i);
	}

	public AbstractExpression(int i) {
		super(i);
	}
	
	public CType getType() {
		return type;
	}

	public void setType(CType type) {
		this.type = type;
	}

	public boolean isMethod() {
		return isMethod;
	}
	
	public Object jjtAccept(CParserVisitor visitor, Object data) {
		return visitor.visit(this, data);
	}
}
