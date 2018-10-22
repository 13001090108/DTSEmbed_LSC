package softtest.summary.c.fault;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import softtest.domain.c.interval.IntegerInterval;
import softtest.interpro.c.Variable;
import softtest.summary.c.MethodFeature;
import softtest.symboltable.c.VariableNameDeclaration;

public class MethodOOBPreCondition extends MethodFeature {
	
	class SubScript {
		IntegerInterval interval;
		String desp;
		
		SubScript(IntegerInterval interval, String desp) {
			this.interval = interval;
			this.desp = desp;
		}

		@Override
		public String toString() {
			return interval.toString()+" "+desp;
		}
	}
	
	private Map<Variable, SubScript> subScriptMap; 
	public final static String METHOD_OOB_PRECONDITION = "METHOD_OOB_PRECONDITION";
	
	public MethodOOBPreCondition() {
		super(METHOD_OOB_PRECONDITION);
		
		subScriptMap = new HashMap<Variable, SubScript>();
	}
	
	/**
	 * Add the subscript constraint information to the map.
	 * @param var
	 * @param interval
	 * @param desp
	 */
	public void addSubScriptVariable(Variable var, IntegerInterval interval, String desp) {
		subScriptMap.put(var, new SubScript(interval, desp));
	}
	
	/**
	 * Check whether exists the information about the specified variable.
	 * @param varDecl
	 * @return
	 */
	public boolean containsSubScriptVar(Variable var) {
		if (var == null) {
			return false;
		}
		
		return subScriptMap.containsKey(var);
	}
	
	/**
	 * Check whether the subscript map is empty or not.
	 * @return
	 */
	public boolean isSubScriptMapEmpty() {
		return subScriptMap.size() == 0;
	}
	
	/**
	 * Get all the variable set in the subscript map.
	 * @return
	 */
	public Set<Variable> getSubScriptVariableSet() {
		return subScriptMap.keySet();
	}
	
	/**
	 * Get the interval for a specified variable.
	 * @param var
	 * @return
	 */
	public IntegerInterval getSubScriptInterval(Variable var) {
		return subScriptMap.get(var).interval;
	}
	
	/**
	 * Get the description for a specified variable.
	 * @param var
	 * @return
	 */
	public String getSubScriptDesp(Variable var) {
		return subScriptMap.get(var).desp;
	}
	
	@Override
	public String toString() {
		StringBuffer sb=new StringBuffer();
		sb.append(name+" : ");
		sb.append(subScriptMap.toString());
		return sb.toString();
	}
}	
