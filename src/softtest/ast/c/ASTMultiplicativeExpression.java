/* Generated By:JJTree: Do not edit this line. ASTMultiplicativeExpression.java Version 4.3 */
/* JavaCCOptions:MULTI=true,NODE_USES_PARSER=true,VISITOR=true,TRACK_TOKENS=false,NODE_PREFIX=AST,NODE_EXTENDS=,NODE_FACTORY=,SUPPORT_CLASS_VISIBILITY_PUBLIC=true */
package softtest.ast.c;

public class ASTMultiplicativeExpression extends AbstractExpression {
	public ASTMultiplicativeExpression(int id) {
		super(id);
	}

	public ASTMultiplicativeExpression(CParser p, int id) {
		super(p, id);
	}

	/** Accept the visitor. * */
	public Object jjtAccept(CParserVisitor visitor, Object data) {
		return visitor.visit(this, data);
	}
}
/*
 * JavaCC - OriginalChecksum=8ec250254d2e376bbb43308e693932f5 (do not edit this
 * line)
 */
