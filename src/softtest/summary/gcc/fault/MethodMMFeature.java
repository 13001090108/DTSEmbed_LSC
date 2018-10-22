package softtest.summary.gcc.fault;


import java.util.HashMap;
import java.util.Set;

import softtest.interpro.c.Variable;
import softtest.summary.c.MMFetureType;
import softtest.summary.c.MethodFeature;
import softtest.symboltable.c.MethodNameDeclaration;

/**
 * 
 * @author Owner
 *
 */
public class MethodMMFeature extends MethodFeature {
	
	public final static String RETURN_VALUE = "__Method__Return__";
	
	public final static String METHOD_MM_FEATURE = "METHOD_MLF_FEATURE";
	
	private HashMap<Variable, MMFetureType> varMalloced;
	private HashMap<Variable, String> desp;
	
	private boolean isAllocateAndReturn = false;
	private MMFetureType mmReturnType;
	private String retTrace = "";
	public MethodMMFeature() {
		super(METHOD_MM_FEATURE);
		varMalloced = new HashMap<Variable,MMFetureType>();
		desp = new HashMap<Variable, String>();
	}

	public HashMap<Variable, MMFetureType> getMMFetures() {
		return varMalloced;
	}
	
	public void addMMVariable(Variable nd,MMFetureType type){
		varMalloced.put(nd, type);
	}

	public boolean isAllocateAndReturn() {
		return isAllocateAndReturn;
	}

	public MMFetureType getMMRetrunType() {
		return this.mmReturnType;
	}
	
	public void setAllocateAndReturn(boolean isAllocateAndReturn, MMFetureType mmReturnType) {
		this.isAllocateAndReturn = isAllocateAndReturn;
		this.mmReturnType = mmReturnType;
	}
	
	public Set<Variable> getMMVariable(){
		return varMalloced.keySet();
	}
	
	public boolean isEmpty() {
		return varMalloced.size() == 0 && !isAllocateAndReturn;
	}
	
	public boolean isContain(Variable variable) {
		return varMalloced.containsKey(variable);
	}
	
	public MMFetureType getMMType(Variable variable) {
		return varMalloced.get(variable);
	}
	
	public void addDesp(Variable var, String desp) {
		this.desp.put(var, desp);
	}
	
	public String getDesp(Variable var) {
		return desp.get(var);
	}
	
	public void setRetTrace(String retTrace) {
		this.retTrace = retTrace;
	}
	
	public String getRetTrace() {
		return retTrace;
	}
	@Override
	public String toString() {
		StringBuffer sb = new StringBuffer();
		sb.append(this.name);
		for (Variable var : varMalloced.keySet()) {
			sb.append(" = " + var.toString());
			sb.append(" [");
			sb.append(varMalloced.get(var));
			sb.append("]");
		}
		if (isAllocateAndReturn) {
			sb.append(" Return " + mmReturnType);
		}
		return sb.toString();
	}

	public MethodNameDeclaration getReleaseMethod() {
		// TODO Auto-generated method stub
		return null;
	}
}
