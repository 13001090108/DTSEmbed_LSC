package softtest.symboltable.c;

import java.io.Serializable;

import softtest.ast.c.SimpleNode;
import softtest.symboltable.c.Type.*;

public abstract class AbstractNameDeclaration implements NameDeclaration,Serializable {
	protected String name = null;//by xiaoyifei
	protected SimpleNode node;
	protected String fileName;
	protected CType type;
	protected Scope scope;
	protected String image;
	
	public AbstractNameDeclaration(SimpleNode node) {
		this.fileName = node.getFileName();
		this.node = node;
		this.scope = node.getScope();
		this.image=node.getImage();
		this.name = node.getImage();
	}
	
	//add by zhouhb
	//2011.4.28
	public AbstractNameDeclaration(String fileName,Scope scope,String image,SimpleNode node) {
		this.fileName = fileName;
		this.scope = scope;
		this.image=image;
		this.node=node;
		this.name = image;
	}
	//end by zhouhb
	
	public String getFileName() {
		return this.fileName;
	}
	
	public void setFileName(String name){
		this.fileName=name;
	}
	
	public String getImage(){
		return this.image;
	}
	
	public SimpleNode getNode() {
		return node;
	}
	public void setNode(SimpleNode node) {
		this.node = node;
	}
	
	public void setName(String name){
		this.name = name;
	}
	
	public String getName(){
		return this.name;
	}
	
	public Scope getScope() {
		return scope;
	}
	
	public void setImage(String image){
		this.image = image;
	}
	
	public void setScope(Scope scope) {
		this.scope = scope;
	}

	public CType getType() {
		return type;
	}

	public void setType(CType type) {
		this.type = type;
	}
	
	@Override
	public String toString() {
		if (this.type == null)
			return getImage() + "!!!";
		return getImage()
				+ " < "
				+ type.toString() + " >";
	}
}
