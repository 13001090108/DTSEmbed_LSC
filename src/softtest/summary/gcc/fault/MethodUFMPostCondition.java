package softtest.summary.gcc.fault;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import softtest.interpro.c.Variable;
import softtest.summary.c.MethodFeature;
import softtest.symboltable.c.VariableNameDeclaration;

/**
 * @author cjie
 * UFM模式的后置信息，提取函数中被delete、free的全局、类成员指针变量 
 */
public class MethodUFMPostCondition extends MethodFeature {
	
	public final static String METHOD_UFM_POSTCONDITION = "METHOD_UFM_POSTCONDITION";
	
	/**
	 * key 函数释放的全局、类成员变量
	 * value 变量对应的后置描述，有可能向上层调用函数传递 
	 */
	private Map<Variable, ArrayList<String>> varList;
	
	public MethodUFMPostCondition() {
		super(METHOD_UFM_POSTCONDITION);
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
	
	/**
	 * 移除某个变量的后置信息 
	 */
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
	
	public Set<Variable> getUFMVariables() {
		return varList.keySet();
	}
	
	public ArrayList<String> getDesp(Variable var) {
		return varList.get(var);
	}
	
	public String getDespString(Variable var) {
		ArrayList<String> desps = varList.get(var);
		String re = "\"" + var.getName() + "\" in ";
		re = "\"" + var.getName() + "\"";
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
