/* Generated By:JJTree: Do not edit this line. ASTCastExpression.java Version 4.3 */
/* JavaCCOptions:MULTI=true,NODE_USES_PARSER=true,VISITOR=true,TRACK_TOKENS=false,NODE_PREFIX=AST,NODE_EXTENDS=,NODE_FACTORY=,SUPPORT_CLASS_VISIBILITY_PUBLIC=true */
package softtest.ast.c;

public
class ASTCastExpression extends AbstractExpression {
  public ASTCastExpression(int id) {
    super(id);
  }

  public ASTCastExpression(CParser p, int id) {
    super(p, id);
  }


  /** Accept the visitor. **/
  public Object jjtAccept(CParserVisitor visitor, Object data) {
    return visitor.visit(this, data);
  }
}
/* JavaCC - OriginalChecksum=a300fb91fea9eb60557257ea449cd7d9 (do not edit this line) */
