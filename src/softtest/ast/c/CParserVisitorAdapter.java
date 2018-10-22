package softtest.ast.c;

public class CParserVisitorAdapter implements CParserVisitor {

	public Object visit(SimpleNode node, Object data) {
		
		node.childrenAccept(this, data);
		return null;
	}

	public Object visit(ASTTranslationUnit node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTExternalDeclaration node, Object data) {
		return visit((SimpleNode) node, data);
	}
	

	public Object visit(ASTInterrupt node, Object data) {
		return visit((SimpleNode) node, data);
	}
	
	public Object visit(ASTMemoryModel node, Object data) {
		return visit((SimpleNode) node, data);
	}
	
	public Object visit(ASTReentrant node, Object data) {
		return visit((SimpleNode) node, data);
	}
	
	public Object visit(ASTUsing node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTFunctionDefinition node, Object data) {
		return visit((SimpleNode) node, data);
	}
	
	public Object visit(ASTFunctionDeclaration node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTDeclaration node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTDeclarationList node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTDeclarationSpecifiers node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTStorageClassSpecifier node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTTypeSpecifier node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTTypeQualifier node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTStructOrUnionSpecifier node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTStructOrUnion node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTStructDeclarationList node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTInitDeclaratorList node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTInitDeclarator node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTStructDeclaration node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTSpecifierQualifierList node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTStructDeclaratorList node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTStructDeclarator node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTEnumSpecifier node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTEnumeratorList node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTEnumerator node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTDeclarator node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTDirectDeclarator node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTPointer node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTTypeQualifierList node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTParameterTypeList node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTParameterList node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTParameterDeclaration node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTIdentifierList node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTInitializer node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTInitializerList node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTTypeName node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTAbstractDeclarator node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTDirectAbstractDeclarator node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTTypedefName node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTStatement node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTLabeledStatement node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTExpressionStatement node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTCompoundStatement node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTStatementList node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTSelectionStatement node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTIterationStatement node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTJumpStatement node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTAssignmentOperator node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTUnaryOperator node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTPriority node, Object data)
	{
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTTask node, Object data)
	{
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTNestedFunctionDeclaration node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTNestedFunctionDefinition node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTLabelDeclarationList node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTLabelDeclaration node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTLabelDeclaratorList node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTLabelDeclarator node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTLabelType node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(ASTTypeofDeclarationSpecifier node, Object data) {
		return visit((SimpleNode) node, data);
	}

	public Object visit(AbstractExpression node, Object data) {
		return visit((SimpleNode) node, data);
	}
	
	public Object visit(ASTPRAGMA node, Object data) {
		return visit((SimpleNode) node, data);
	}
	
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
	 */
	
	public Object visit(ASTAdditiveExpression node, Object data) {
		return visit((AbstractExpression) node, data);
	}
	
	public Object visit(ASTANDExpression node, Object data) {
		return visit((AbstractExpression) node, data);
	}
	
	public Object visit(ASTArgumentExpressionList node, Object data) {
		return visit((AbstractExpression) node, data);
	}
	
	public Object visit(ASTAssignmentExpression node, Object data) {
		return visit((AbstractExpression) node, data);
	}
	
	public Object visit(ASTCastExpression node, Object data) {
		return visit((AbstractExpression) node, data);
	}
	
	public Object visit(ASTConditionalExpression node, Object data) {
		return visit((AbstractExpression) node, data);
	}
	
	public Object visit(ASTConstant node, Object data) {
		return visit((AbstractExpression) node, data);
	}
	
	public Object visit(ASTConstantExpression node, Object data) {
		return visit((AbstractExpression) node, data);
	}
	
	public Object visit(ASTEqualityExpression node, Object data) {
		return visit((AbstractExpression) node, data);
	}
	
	public Object visit(ASTExclusiveORExpression node, Object data) {
		return visit((AbstractExpression) node, data);
	}
	
	public Object visit(ASTExpression node, Object data) {
		return visit((AbstractExpression) node, data);
	}
	
	public Object visit(ASTFieldId node, Object data) {
		return visit((AbstractExpression) node, data);
	}
	
	public Object visit(ASTInclusiveORExpression node, Object data) {
		return visit((AbstractExpression) node, data);
	}
	
	public Object visit(ASTLogicalANDExpression node, Object data) {
		return visit((AbstractExpression) node, data);
	}
	
	public Object visit(ASTLogicalORExpression node, Object data) {
		return visit((AbstractExpression) node, data);
	}
	
	public Object visit(ASTMultiplicativeExpression node, Object data) {
		return visit((AbstractExpression) node, data);
	}
	
	public Object visit(ASTPostfixExpression node, Object data) {
		return visit((AbstractExpression) node, data);
	}
	
	public Object visit(ASTPrimaryExpression node, Object data) {
		return visit((AbstractExpression) node, data);
	}
	
	public Object visit(ASTRelationalExpression node, Object data) {
		return visit((AbstractExpression) node, data);
	}
	
	public Object visit(ASTShiftExpression node, Object data) {
		return visit((AbstractExpression) node, data);
	}
	
	public Object visit(ASTUnaryExpression node, Object data) {
		return visit((AbstractExpression) node, data);
	}
}
