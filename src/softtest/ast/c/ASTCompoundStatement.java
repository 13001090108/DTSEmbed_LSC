/* Generated By:JJTree: Do not edit this line. ASTCompoundStatement.java Version 4.3 */
/* JavaCCOptions:MULTI=true,NODE_USES_PARSER=true,VISITOR=true,TRACK_TOKENS=false,NODE_PREFIX=AST,NODE_EXTENDS=,NODE_FACTORY=,SUPPORT_CLASS_VISIBILITY_PUBLIC=true */
package softtest.ast.c;

public
class ASTCompoundStatement extends SimpleNode {
  public ASTCompoundStatement(int id) {
    super(id);
  }

  public ASTCompoundStatement(CParser p, int id) {
    super(p, id);
  }


  /** Accept the visitor. **/
  public Object jjtAccept(CParserVisitor visitor, Object data) {
    return visitor.visit(this, data);
  }
}
/* JavaCC - OriginalChecksum=7cb37f68fd9ded60e6dfb60c85a637e5 (do not edit this line) */
