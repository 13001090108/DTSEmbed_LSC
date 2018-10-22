package softtest.summary.gcc.fault;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import softtest.interpro.c.Variable;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.summary.c.MethodFeature;
import softtest.summary.gcc.fault.IAOType;

public class MethodIAOPreCondition extends MethodFeature {

	public final static String METHOD_IAO_PRECONDITION = "METHOD_IAO_PRECONDITION";
	private Map<Variable, IAOInfo> varList;
	
	//使用内部类存储IAO变量对应的信息：对应IAO类型，错误描述信息
	public class IAOInfo {
		private String funcName;
		private IAOType type;
		private String des;
		
		public IAOInfo(IAOType type, String funcName, String des) {
			this.type = type;
			this.funcName = funcName;
			this.des = des;
		}
		
		public IAOType getIAOType() {
			return type;
		}
		
		public String getDes() {
			return des;
		}
		
		public String getFuncName() {
			return funcName;
		}
	}
	
	public MethodIAOPreCondition() {
		super(METHOD_IAO_PRECONDITION);
		varList = new HashMap<Variable, IAOInfo>();
	}
	
	/**
	 * 添加指定变量及约束信息到前置约束中
	 */
	public void addVariable(Variable var, IAOType type, String funcName, String des) {
		varList.put(var, new IAOInfo(type, funcName, des));
	}
	/**
	 * 添加指定变量及约束信息到前置约束中
	 */
	public void addVariable(Variable var, IAOInfo info) {
		varList.put(var, info);
	}
	/**
	 * 判断IAO前置约束是否包含对某变量的约束
	 * @param var
	 * @return
	 */
	public boolean contains(VariableNameDeclaration var) {
		Variable variable = Variable.getVariable(var);
		if (variable == null) {
			return false;
		}
		return varList.containsKey(variable); 
	}
	
	/**
	 * 获取前置条件中某指定变量的区间约束
	 * @param var
	 * @return
	 */
	public IAOInfo getIAOInfo(Variable var) {
		return varList.get(var);
	}
	
	/**
	 * 判断该IAO前置约束是否为空
	 * @return
	 */
	public boolean isEmpty() {
		return varList.size() == 0;
	}
	
	public Set<Variable> getIAOVariables() {
		return varList.keySet();
	}
	
	/**
	 * 得到当前相应变量var的type
	 */
	public IAOType getIAOType(Variable var) {
		return getIAOInfo(var).type;
	}
	
	/**
	 * 得到当前相应变量var的description
	 */
	public String getIAODesp(Variable var) {
		return getIAOInfo(var).des;
	}
	
	@Override
	public String toString() {
		StringBuffer sb = new StringBuffer();
		sb.append(this.name);
		for (Variable var : varList.keySet()) {
			sb.append(" = " + var.toString());
			sb.append(" [");
			sb.append(varList.get(var) + " ");
			sb.append("]");
		}
		return sb.toString();
	}
	
}
