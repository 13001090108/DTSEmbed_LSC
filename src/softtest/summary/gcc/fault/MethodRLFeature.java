package softtest.summary.gcc.fault;

import java.util.HashMap;
import java.util.Set;

import softtest.interpro.c.Method;
import softtest.interpro.c.Variable;
import softtest.summary.c.MethodFeature;

public class MethodRLFeature extends MethodFeature{

	public final static String METHOD_RL_FEATURE = "METHOD_RL_FEATURE";
	
	private HashMap<Variable, Method> varAllocFree;
	
	//函数特征的描述信息
	private HashMap<Variable, String> desp;
	
	private boolean isAllocateAndReturn = false;
    
	private Method allocMethod;//用于直接返回资源特征传递时标识方法，我承认设计得不好，欢迎指正
	private Method releaseMethod;
	private String retTrace = "";
	
	public MethodRLFeature() {
		super(METHOD_RL_FEATURE);
		varAllocFree = new HashMap<Variable,Method>();
		desp = new HashMap<Variable, String>();
	}
	public boolean isAllocateAndReturn() {
		return isAllocateAndReturn;
	}
	public void setAllocateAndReturn(boolean isAllocateAndReturn) {
		this.isAllocateAndReturn = isAllocateAndReturn;
	}
	
	public void addDesp(Variable var, String desp) {
		this.desp.put(var, desp);
	}
	
	public HashMap<Variable, String> getAllDesp(){
		return desp;
	}
	
	public String getDesp(Variable var) {
		return desp.get(var);
	}
	
	public HashMap<Variable, Method> getRLFetures() {
		return varAllocFree;
	}
	
	public void setRetTrace(String retTrace) {
		this.retTrace = retTrace;
	}
	
	public String getRetTrace() {
		return retTrace;
	}
	/**
	 * 判断该RL特征摘要是否为空
	 */
	public boolean isEmpty() {
		return varAllocFree.isEmpty() && !isAllocateAndReturn;
	}
	
	/**
	 * 判断RL特征摘要是否包含某变量
	 */
	public boolean isContain(Variable variable) {
		return varAllocFree.containsKey(variable);
	}
	
	public Set<Variable> getRLVariable(){
		return varAllocFree.keySet();
	}
	
	/**
	 * 添加指定变量及约束信息到前置约束中
	 */
	public void addVariable(Variable var, Method methodName) {
		varAllocFree.put(var, methodName);
	}
	
	public Method getMethodNameDeclaration(Variable var) {
		if(var == null)
			return null;
		return varAllocFree.get(var);
	}
	public void setRelatedReleasedMethod(Method releaseMethod) {
		this.releaseMethod = releaseMethod;
		
	}
	public Method getRelatedReleasedMethod() {
		return this.releaseMethod;
		
	}
	public void setAllocMethod(Method allocMethod) {
		this.allocMethod = allocMethod;
	}
	public Method getAllocMethod() {
		return allocMethod;
	}
}
