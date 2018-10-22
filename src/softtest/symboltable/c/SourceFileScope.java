package softtest.symboltable.c;

import java.util.*;

import softtest.ast.c.*;


public class SourceFileScope extends AbstractScope implements Scope {

	protected Map<ClassNameDeclaration, ArrayList<NameOccurrence>> classNames;
	protected Map<MethodNameDeclaration, ArrayList<NameOccurrence>> methodNames;
	protected Map<VariableNameDeclaration, ArrayList<NameOccurrence>> variableNames;
	public int varIndex=0;
	
	public int getVarIndex() {
		return varIndex++;
	}
	public SourceFileScope(SimpleNode node) {
		this.node = node;
		classNames = new HashMap<ClassNameDeclaration, ArrayList<NameOccurrence>>();
		methodNames = new HashMap<MethodNameDeclaration, ArrayList<NameOccurrence>>();
		variableNames = new HashMap<VariableNameDeclaration, ArrayList<NameOccurrence>>();
	}


	@Override
	public SourceFileScope getEnclosingSourceFileScope() {
		return this;
	}

	public void addDeclaration(VariableNameDeclaration variableDecl) {
		variableDecl.setScope(this);
		variableNames.put(variableDecl, new ArrayList<NameOccurrence>());
	}

	public void addDeclaration(ClassNameDeclaration classDecl) {
		classDecl.setScope(this);
		classNames.put(classDecl, new ArrayList<NameOccurrence>());
	}

	//zys:由于C中函数不能重载（函数名相同，参数不同），所以不能重复添加		2010.3.7
	public void addDeclaration(MethodNameDeclaration decl) {
		decl.setScope(this);
		
		//zys:由于C中函数不能重载（函数名相同，参数不同），所以不能重复添加		2010.3.7
		Set<MethodNameDeclaration> set=methodNames.keySet();
		for(MethodNameDeclaration mnd:set)
		{
			if(mnd.getImage().equals(decl.getImage()))
			{
				return;
			}
		}
		
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
	
	@Override
	public String toString() {
		return "SourceFileScope: (classes:"
				+ glomNames(classNames.keySet().iterator()) + ")" + "(methods:"
				+ glomNames(methodNames.keySet().iterator()) + ")"
				+ "(variables:" + glomNames(variableNames.keySet().iterator())
				+ ")";
	}

	@Override
	public String dump() {
		StringBuffer b = new StringBuffer();
		b.append("SourceFileScope (" + name + "): ");
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

}
