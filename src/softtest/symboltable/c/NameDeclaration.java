package softtest.symboltable.c;

import softtest.ast.c.SimpleNode;
import softtest.symboltable.c.Type.CType;

public interface NameDeclaration {
	public SimpleNode getNode();

	public String getFileName();

	public Scope getScope();
	public String getImage();
	public CType getType();
	
	public void setType(CType type);
}
