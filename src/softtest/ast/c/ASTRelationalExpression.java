/* Generated By:JJTree: Do not edit this line. ASTRelationalExpression.java Version 4.3 */
/* JavaCCOptions:MULTI=true,NODE_USES_PARSER=true,VISITOR=true,TRACK_TOKENS=false,NODE_PREFIX=AST,NODE_EXTENDS=,NODE_FACTORY=,SUPPORT_CLASS_VISIBILITY_PUBLIC=true */
package softtest.ast.c;

public
class ASTRelationalExpression extends AbstractExpression {
  public ASTRelationalExpression(int id) {
    super(id);
  }

  public ASTRelationalExpression(CParser p, int id) {
    super(p, id);
  }


  /** Accept the visitor. **/
  public Object jjtAccept(CParserVisitor visitor, Object data) {
    return visitor.visit(this, data);
  }
}
/* JavaCC - OriginalChecksum=ea83e33660bec54d8e1fb37bb025e595 (do not edit this line) */
