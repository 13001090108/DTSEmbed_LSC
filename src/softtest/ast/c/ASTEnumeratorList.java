/* Generated By:JJTree: Do not edit this line. ASTEnumeratorList.java Version 4.3 */
/* JavaCCOptions:MULTI=true,NODE_USES_PARSER=true,VISITOR=true,TRACK_TOKENS=false,NODE_PREFIX=AST,NODE_EXTENDS=,NODE_FACTORY=,SUPPORT_CLASS_VISIBILITY_PUBLIC=true */
package softtest.ast.c;

public
class ASTEnumeratorList extends SimpleNode {
  public ASTEnumeratorList(int id) {
    super(id);
  }

  public ASTEnumeratorList(CParser p, int id) {
    super(p, id);
  }


  /** Accept the visitor. **/
  public Object jjtAccept(CParserVisitor visitor, Object data) {
    return visitor.visit(this, data);
  }
}
/* JavaCC - OriginalChecksum=5cec6b742b9615c6f42a23d52fd64183 (do not edit this line) */