/* Generated By:JJTree: Do not edit this line. ASTLabelDeclaratorList.java Version 4.3 */
/* JavaCCOptions:MULTI=true,NODE_USES_PARSER=true,VISITOR=true,TRACK_TOKENS=false,NODE_PREFIX=AST,NODE_EXTENDS=,NODE_FACTORY=,SUPPORT_CLASS_VISIBILITY_PUBLIC=true */
package softtest.ast.c;

public
class ASTLabelDeclaratorList extends SimpleNode {
  public ASTLabelDeclaratorList(int id) {
    super(id);
  }

  public ASTLabelDeclaratorList(CParser p, int id) {
    super(p, id);
  }


  /** Accept the visitor. **/
  public Object jjtAccept(CParserVisitor visitor, Object data) {
    return visitor.visit(this, data);
  }
}
/* JavaCC - OriginalChecksum=662f24d1dcdd0aa0941cc9d639903dda (do not edit this line) */
