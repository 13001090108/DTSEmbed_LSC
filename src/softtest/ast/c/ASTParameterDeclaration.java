/* Generated By:JJTree: Do not edit this line. ASTParameterDeclaration.java Version 4.3 */
/* JavaCCOptions:MULTI=true,NODE_USES_PARSER=true,VISITOR=true,TRACK_TOKENS=false,NODE_PREFIX=AST,NODE_EXTENDS=,NODE_FACTORY=,SUPPORT_CLASS_VISIBILITY_PUBLIC=true */
package softtest.ast.c;

import softtest.symboltable.c.Type.CType;

public class ASTParameterDeclaration extends SimpleNode {
	CType type = null;
	
	String identifier = "";

	public ASTParameterDeclaration(int id) {
		super(id);
	}

	public CType getType() {
		return type;
	}

	public void setType(CType type) {
		this.type = type;
	}

	public ASTParameterDeclaration(CParser p, int id) {
		super(p, id);
	}

	/** Accept the visitor. **/
	public Object jjtAccept(CParserVisitor visitor, Object data) {
		return visitor.visit(this, data);
	}

	public String getIdentifier() {
		return identifier;
	}

	public void setIdentifier(String identifier) {
		this.identifier = identifier;
	}
	

}
/* JavaCC - OriginalChecksum=09162dea631cfc7bf823305f8e20ab3f (do not edit this line) */
