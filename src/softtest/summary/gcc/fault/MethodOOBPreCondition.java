package softtest.summary.gcc.fault;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import softtest.domain.c.interval.IntegerInterval;
import softtest.interpro.c.Variable;
import softtest.summary.c.MethodFeature;

/*
* modified by nmh
* 增加一个参数flag
* 如果已知的区间要比所约束的区间大，则flag = 0
* 如果已知的区间要比所约束的区间小，则flag = 1
*/
public class MethodOOBPreCondition extends MethodFeature {
	
	class SubScript {
		IntegerInterval interval;
		String desp;
		int flag;
		int index;//标志结构体的第几个成员
		
		SubScript(IntegerInterval interval, String desp, int flag,int index) {
			this.interval = interval;
			this.desp = desp;
			this.flag = flag;
			this.index = index;
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
	public void addSubScriptVariable(Variable var, IntegerInterval interval, String desp,int flag) {
		subScriptMap.put(var, new SubScript(interval, desp, flag, -1));
	}
	
	public void addSubScriptVariable(Variable var, IntegerInterval interval, String desp,int flag,int index) {
		subScriptMap.put(var, new SubScript(interval, desp, flag, index));
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
	
	/**
	 * Get the flag for a specified variable.
	 * @param var
	 * @return
	 */
	public int getSubScriptFlag(Variable var) {
		return subScriptMap.get(var).flag;
	}
	
	/**
	 * Get the index for a specified variable.
	 * @param var
	 * @return
	 */
	public int getSubScriptIndex(Variable var) {
		return subScriptMap.get(var).index;
	}
}	
