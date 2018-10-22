package softtest.summary.gcc.fault;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import softtest.config.c.Config;
import softtest.interpro.c.Variable;
import softtest.summary.c.MethodFeature;
import softtest.symboltable.c.VariableNameDeclaration;

/**
 *  
 */
public class MethodMMPreCondition extends MethodFeature {
	
	public final static String METHOD_MM_PRECONDITION = "METHOD_MM_PRECONDITION";
	
	/**
	 * key 函数释放的全局、类成员变量
	 * value 变量对应的后置描述，有可能向上层调用函数传递 
	 */
	private Map<Variable, ArrayList<String>> varList;
	
	public MethodMMPreCondition() {
		super(METHOD_MM_PRECONDITION);
		varList = new HashMap<Variable, ArrayList<String>>();
	}
	public void addVariable(Variable var, String des) {
		ArrayList<String> desList = null;
		if (varList.get(var) == null) {
			desList = new ArrayList<String>();
			varList.put(var, desList);
		} else {
			desList = varList.get(var);
		}
		desList.add(des);
	}
	
	public void addVariable(Variable var, ArrayList<String> des) {
		varList.put(var, des);
	}
	

	public boolean removeVariable(Variable var) {
		ArrayList<String> desList = varList.remove(var);
		return desList != null;
	}
	
	public boolean contains(VariableNameDeclaration var) {
		Variable variable = Variable.getVariable(var);
		if (variable == null) {
			return false;
		}
		return varList.containsKey(variable); 
	}
	
	public boolean contains(Variable var) {
		if(var == null) {
			return false;
		}
		return varList.containsKey(var);
	}
	
	public Set<Variable> getVariables() {
		return varList.keySet();
	}
	
	public ArrayList<String> getDesp(Variable var) {
		return varList.get(var);
	}
	
	public String getDespString(Variable var) {
		ArrayList<String> desps = varList.get(var);
		String re = "\"" + var.getName() + "\" in ";
		if (Config.DTS_LANGUAGE == Config.LANG_CHINESE) {
			re = "\"" + var.getName() + "\"";
		}
		for (String desp : desps) {
			re += ", " + desp;
		}
		return re;
	}
	
	public boolean isEmpty() {
		return varList.size() == 0;
	}
	
	@Override
	public String toString() {
		StringBuffer sb = new StringBuffer();
		sb.append(this.name);
		for (Variable var : varList.keySet()) {
			sb.append(" = " + var.toString());
			sb.append(" [");
			for (String des : varList.get(var)) {
				sb.append(des + " ");
			}
			sb.append("]");
		}
		return sb.toString();
	}
	
}
