/* Generated By:JJTree: Do not edit this line. ASTTask.java Version 4.3 */
/* JavaCCOptions:MULTI=true,NODE_USES_PARSER=true,VISITOR=true,TRACK_TOKENS=false,NODE_PREFIX=AST,NODE_EXTENDS=,NODE_FACTORY=,SUPPORT_CLASS_VISIBILITY_PUBLIC=true */
package softtest.ast.c;

public class ASTTask extends SimpleNode {
	String tasknum = "";

	public String getTasknum() {
		return tasknum;
	}

	public void setTasknum(String tasknum) {
		this.tasknum = tasknum;
	}

	public ASTTask(int id) {
		super(id);
	}

	public ASTTask(CParser p, int id) {
		super(p, id);
	}

	/** Accept the visitor. **/
	public Object jjtAccept(CParserVisitor visitor, Object data) {
		return visitor.visit(this, data);
	}
}
/* JavaCC - OriginalChecksum=0ab2c69d09120a6209ba514088980781 (do not edit this line) */
