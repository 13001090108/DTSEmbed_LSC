package softtest.symboltable.c;

import java.util.*;

import softtest.ast.c.SimpleNode;
import softtest.callgraph.c.CGraph;
import softtest.symboltable.c.Type.*;
import softtest.symboltable.c.NameOccurrence;
import softtest.symboltable.c.VariableNameDeclaration;

public interface Scope
{
	public Map<VariableNameDeclaration, ArrayList<NameOccurrence>>getVariableDeclarations();
	
	Map getMethodDeclarations();
	
	Map getClassDeclarations();
	
	//
	public int getVarIndex();

	void addDeclaration(ClassNameDeclaration decl);

	void addDeclaration(VariableNameDeclaration decl);

	void addDeclaration(MethodNameDeclaration decl);


	boolean isSelfOrAncestor(Scope ancestor);

	void addNameOccurrence(NameDeclaration decl,NameOccurrence occ);

	void setParent(Scope parent);
	public SimpleNode getNode();
	Scope getParent();

	ClassScope getEnclosingClassScope();

	SourceFileScope getEnclosingSourceFileScope();

	MethodScope getEnclosingMethodScope();

	List<Scope> getChildrens();	
	
	String print();
	
	public CType getType(String name);
	
	public void addType(String name, CType type);
	
	public String getName();

	void resolveCallRelation(CGraph g);
}
