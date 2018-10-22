package softtest.symboltable.c;

import java.util.*;
import softtest.ast.c.*;


public class ClassScope extends AbstractScope {

	protected Map<MethodNameDeclaration, ArrayList<NameOccurrence>> methodNames;

	protected Map<ClassNameDeclaration, ArrayList<NameOccurrence>> classNames;

	protected Map<VariableNameDeclaration, ArrayList<NameOccurrence>> variableNames;


	private ClassScope() {
		methodNames = new HashMap<MethodNameDeclaration, ArrayList<NameOccurrence>>();
		variableNames = new HashMap<VariableNameDeclaration, ArrayList<NameOccurrence>>();
		classNames = new HashMap<ClassNameDeclaration, ArrayList<NameOccurrence>>();
	}

	public ClassScope(String name, SimpleNode node) {
		this();
		this.name = name;
		this.node = node;
	}

	public String getName() {
		return name;
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

	public Map<VariableNameDeclaration, ArrayList<NameOccurrence>> getVariableDeclarations() {
		return variableNames;
	}

	public Map<MethodNameDeclaration, ArrayList<NameOccurrence>> getMethodDeclarations() {
		return methodNames;
	}

	public Map<ClassNameDeclaration, ArrayList<NameOccurrence>> getClassDeclarations() {
		return classNames;
	}

	public ClassScope getEnclosingClassScope() {
		return this;
	}

	public String getClassName() {
		return this.name;
	}

	public String toString() {
		return "ClassScope(" + this.getName() + "): " + "(methods:"
				+ glomNames(methodNames.keySet().iterator()) + ")(variables:"
				+ glomNames(variableNames.keySet().iterator()) + ")";
	}
	
	@Override
	public String dump() {
		StringBuffer b = new StringBuffer();
		b.append("ClassScope (" + name + "): ");
		if (!classNames.isEmpty()) {
			b.append("(classes: ");
			Iterator i = classNames.keySet().iterator();
			while (i.hasNext()) {
				ClassNameDeclaration mnd = (ClassNameDeclaration) i.next();
				b.append(mnd.toString());
				if (i.hasNext()) {
					b.append(",");
				}
			}
			b.append(")");
		}
		if (!methodNames.isEmpty()) {
			b.append("(methods: ");
			Iterator i = methodNames.keySet().iterator();
			while (i.hasNext()) {
				MethodNameDeclaration mnd = (MethodNameDeclaration) i.next();
				b.append(mnd.toString());
				if (i.hasNext()) {
					b.append(",");
				}
			}
			b.append(")");
		}
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

	/**
	 * 将当前类作用域中所有与抽象语法树节点关联耦合的对象全部解耦合
	 * zys:待实现
	 */
	public void deRefrence() {
		
	}
}
