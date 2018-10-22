package softtest.scvp.c;

import java.io.Serializable;

import softtest.ast.c.ASTFunctionDefinition;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.VexNode;
import softtest.interpro.c.Method;
import softtest.symboltable.c.NameOccurrence;

public class Position implements Serializable{
	/**
	 * @author cmershen
	 */
	
	private String fileName;
	private String functionName;
	private Method method;
	private int beginLine,endLine;
	//added by cmershen,2016.10.18 增加函数调用的索引
	private boolean isFunction;
	private int index;
	public String getFileName() {
		return fileName;
	}
	public void setFileName(String fileName) {
		this.fileName = fileName;
	}
	public String getFunctionName() {
		return functionName;
	}
	public void setFunctionName(String functionName) {
		this.functionName = functionName;
	}
	public int getBeginLine() {
		return beginLine;
	}
	public void setBeginLine(int beginLine) {
		this.beginLine = beginLine;
	}
	public int getEndLine() {
		return endLine;
	}
	public void setEndLine(int endLine) {
		this.endLine = endLine;
	}
	public Position(VexNode n,SimpleNode node) {
		fileName = n.getTreenode().getFileName();
		functionName = n.getGraph().getEntryNode().getTreenode().getImage();
		String[] temp = fileName.split("\\\\");
		fileName = temp[temp.length-1];
		beginLine = node.getBeginLine();
		endLine = node.getEndLine();
		ASTFunctionDefinition methodNode = (ASTFunctionDefinition)n.getGraph().getEntryNode().getTreenode();
		method=methodNode.getDecl().getMethod();
		isFunction = false;
	}
	public Position(VexNode n,NameOccurrence occ) {
		
		fileName = n.getTreenode().getFileName();
		functionName = n.getGraph().getEntryNode().getTreenode().getImage();
		String[] temp = fileName.split("\\\\");
		fileName = temp[temp.length-1];
		beginLine = occ.getLocation().getBeginLine();
		endLine = occ.getLocation().getEndLine();
		ASTFunctionDefinition methodNode = (ASTFunctionDefinition)n.getGraph().getEntryNode().getTreenode();
		method=methodNode.getDecl().getMethod();
		isFunction = false;
	}
	public Position() {
		super();
	}
	public Method getMethod() {
		return method;
	}
	public void setMethod(Method method) {
		this.method = method;
	}
//	@Override
//	public String toString() {
//		return "Position [fileName=" + fileName + ", method=" + method
//				+ ", beginLine=" + beginLine + ", endLine=" + endLine + "]";
//	}
	@Override
	public String toString() {
		if(isFunction)
			return "Position [fileName=" + fileName + ", functionName=" + functionName + ", method=" + method
					+ ", beginLine=" + beginLine + ", endLine=" + endLine + ", index=" + index + "]";
		else
			return "Position [fileName=" + fileName + ", method=" + method
					+ ", beginLine=" + beginLine + ", endLine=" + endLine + "]";
	}
	public boolean isFunction() {
		return isFunction;
	}
	public void setFunction(boolean isFunction) {
		this.isFunction = isFunction;
	}
	public int getIndex() {
		return index;
	}
	public void setIndex(int index) {
		this.index = index;
	}
	public String getfileName() {
		return fileName;
	}
	public String getfunctionName() {
		return functionName;
	}
}
