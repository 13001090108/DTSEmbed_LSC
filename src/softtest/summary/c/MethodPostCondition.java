package softtest.summary.c;

import java.util.HashMap;
import java.util.Map;
import softtest.domain.c.interval.Domain;
import softtest.interpro.c.Variable;
/**
 * 
 * @author ∆Ó≈Ù
 *
 */
public class MethodPostCondition extends MethodFeature {
	
	public final static String METHOD_POST_CONDITION = "METHOD_POST_CONDITION";
	
	private Map<Variable, Domain> variables;
	
	public MethodPostCondition() {
		super(METHOD_POST_CONDITION);
		variables = new HashMap<Variable, Domain>();
	}
	
	public void addDomain(Variable variable, Domain domain) {
		variables.put(variable, domain);
	}
	
	public Map<Variable, Domain> getPostConds() {
		return variables;
	}
	
	public Domain getDomain(Variable variable) {
		return variables.get(variable);
	}
	
	public boolean isEmpty() {
		return variables.isEmpty();
	}
	
	@Override
	public String toString() {
		StringBuffer sb = new StringBuffer();
		sb.append(this.name);
		for (Variable var : variables.keySet()) {
			sb.append(" £∫ " + var.toString() + " ");
			sb.append(variables.get(var) + "; ");
		}
		return sb.toString();
	}
}
