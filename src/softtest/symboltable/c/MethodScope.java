package softtest.symboltable.c;

import java.util.*;

import softtest.ast.c.*;


public class MethodScope extends AbstractScope {

	protected Map<VariableNameDeclaration, ArrayList<NameOccurrence>> variableNames;
	
	private SimpleNode node;

	public MethodScope(SimpleNode node) {
		variableNames = new HashMap<VariableNameDeclaration,ArrayList<NameOccurrence>>();
		this.node = node;
	} 

	//added by xqing
	public SimpleNode getAstTreeNode() {
		return node;
	}
	@Override
	public MethodScope getEnclosingMethodScope() {
		return this;
	}
	
	public void  addNameOccurrence(NameDeclaration decl,NameOccurrence occurrence) {
		if (decl instanceof VariableNameDeclaration) {
			List<NameOccurrence> nameOccurrences = variableNames.get(decl);
			nameOccurrences.add(occurrence);
		}
	}

	public Map<VariableNameDeclaration, ArrayList<NameOccurrence>> getVariableDeclarations() {
		return variableNames;
	}
	
	public void addDeclaration(VariableNameDeclaration nameDecl) {
		nameDecl.setScope(this);
		variableNames.put(nameDecl, new ArrayList<NameOccurrence>());
	}


	@Override
	public String toString() {
		return "MethodScope(" + this.getName() + "): " + "(variables:"
					+ glomNames(variableNames.keySet().iterator()) + ")";
	}
	
	@Override
	public String dump() {
		StringBuffer b = new StringBuffer();
		b.append("MethodScope(" + getName() + "): ");
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
	@Override
	public void updateDeclaration(VariableNameDeclaration varDecl) {
		for (VariableNameDeclaration var : variableNames.keySet()) {
			if (var.getVariable().getName().equals(varDecl.getVariable().getName())) {
				var.setType(varDecl.getType());
				var.setParamIndex(varDecl.getParamIndex());
			}
		}
	}
}
