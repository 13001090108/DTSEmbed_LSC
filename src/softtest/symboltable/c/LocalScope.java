package softtest.symboltable.c;
import java.util.*;

import softtest.ast.c.*;

public class LocalScope extends AbstractScope {

	protected Map<VariableNameDeclaration, ArrayList<NameOccurrence>> variableNames;
	
	protected Map<MethodNameDeclaration, ArrayList<NameOccurrence>> methodNames;
	
	protected Map<ClassNameDeclaration, ArrayList<NameOccurrence>> classNames;
	
	//dongyk 2012.4.13用于标志数组下标是表达式，一旦发现是expn（n为递增整数），则通过调用真正ExpressionValueVisitor.visit(ASTAssignment)计算出
	//public static int arrIndex=1; 
	
	public LocalScope(SimpleNode node) {
		this.node = node;
		methodNames = new HashMap<MethodNameDeclaration, ArrayList<NameOccurrence>>();
		variableNames = new HashMap<VariableNameDeclaration, ArrayList<NameOccurrence>>();
		classNames = new HashMap<ClassNameDeclaration, ArrayList<NameOccurrence>>();
	}

	public void addNameOccurrence(NameDeclaration decl,NameOccurrence occurrence) {
		if (decl instanceof MethodNameDeclaration) {
			ArrayList<NameOccurrence> nameOccurrences = methodNames.get(decl);
			if (nameOccurrences != null) {
				nameOccurrences.add(occurrence);
			}
		} else if (decl instanceof VariableNameDeclaration) {
			ArrayList<NameOccurrence> nameOccurrences = variableNames.get(decl);
			if (nameOccurrences != null) {
				nameOccurrences.add(occurrence);
			}
		} else if (decl instanceof ClassNameDeclaration) {
			ArrayList<NameOccurrence> nameOccurrences = classNames.get(decl);
			if (nameOccurrences != null) {
				nameOccurrences.add(occurrence);
			}
		} else {
			throw new RuntimeException(
					"This is an incorrect NameDeclaration object");
		}
	}

	public void addDeclaration(VariableNameDeclaration variableDecl) {
		variableDecl.setScope(this);
		variableNames.put(variableDecl, new ArrayList<NameOccurrence>());
	}

	public void addDeclaration(ClassNameDeclaration classDecl) {
		classDecl.setScope(this);
		classNames.put(classDecl, new ArrayList<NameOccurrence>());
	}

	public void addDeclaration(MethodNameDeclaration decl) {
		decl.setScope(this);
		methodNames.put(decl, new ArrayList<NameOccurrence>());
	}

	public Map<VariableNameDeclaration, ArrayList<NameOccurrence>> getVariableDeclarations() {
		return variableNames;
	}

	public Map<MethodNameDeclaration, ArrayList<NameOccurrence>> getMethodDeclarations() {
		return methodNames;
	}

	public Map<ClassNameDeclaration, ArrayList<NameOccurrence>> getClassDeclarations() {
		return classNames;
	}

	@Override
	public String toString() {
		return "LocalScope:"+this.getName()+"::" + "(variables:"
				+ glomNames(variableNames.keySet().iterator()) + ")";
	}
	
	@Override
	public String dump() {
		StringBuffer b = new StringBuffer();
		b.append("LocalScope: ");
		if (!variableNames.isEmpty()) {
			b.append("(variables: ");
			Iterator i = variableNames.keySet().iterator();
			while (i.hasNext()) {
				VariableNameDeclaration mnd = (VariableNameDeclaration) i.next();
				b.append(mnd.toString());
				if (i.hasNext()) {
					b.append(",");
				}
			}
			b.append(")");
		}
		return b.toString();
	}
}
