/* Generated By:JJTree: Do not edit this line. ASTTypeofDeclarationSpecifier.java Version 4.3 */
/* JavaCCOptions:MULTI=true,NODE_USES_PARSER=true,VISITOR=true,TRACK_TOKENS=false,NODE_PREFIX=AST,NODE_EXTENDS=,NODE_FACTORY=,SUPPORT_CLASS_VISIBILITY_PUBLIC=true */
package softtest.ast.c;

import softtest.symboltable.c.Type.CType;

public class ASTTypeofDeclarationSpecifier extends SimpleNode {
	CType type = null;

	public ASTTypeofDeclarationSpecifier(int id) {
		super(id);
	}

	public CType getType() {
		return type;
	}

	public void setType(CType type) {
		this.type = type;
	}

	public ASTTypeofDeclarationSpecifier(CParser p, int id) {
		super(p, id);
	}

	/** Accept the visitor. **/
	public Object jjtAccept(CParserVisitor visitor, Object data) {
		return visitor.visit(this, data);
	}
}
/* JavaCC - OriginalChecksum=edbc12b50a96428c5b6ef9370415757e (do not edit this line) */
