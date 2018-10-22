package softtest.summary.gcc.fault;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import softtest.domain.c.interval.IntegerDomain;
import softtest.summary.c.MethodFeature;
import softtest.summary.gcc.fault.UVF_PInfo.UVF_PType;
import softtest.symboltable.c.VariableNameDeclaration;
/**
 * 函数的指针内容使用摘要，记录当前函数对运行上下文中的指针变量的内容的初始化的约束
 * @author zl
 *
 */
public class MethodUVF_PPreCondition extends MethodFeature{
	public final static String METHOD_UVF_P_PRECONDITION = "METHOD_UVF_P_PRECONDITION";
	private Map<VariableNameDeclaration, UVF_PInfo> varList;
	

	
	public MethodUVF_PPreCondition(){
		super(METHOD_UVF_P_PRECONDITION);
		varList = new HashMap<VariableNameDeclaration, UVF_PInfo>();
	}
	/**
	 * 添加指定变量及约束信息到前置约束中
	 */
	public void addVariable(VariableNameDeclaration var, int paramIndex, UVF_PType type,IntegerDomain needInitedomain,IntegerDomain initedomain) {
		varList.put(var, new UVF_PInfo(var.getImage(), paramIndex, type,needInitedomain,initedomain));
	}
	/**
	 * 添加指定变量及约束信息到前置约束中
	 */
	public void addVariable(VariableNameDeclaration var, UVF_PInfo info) {
		varList.put(var, info);
	}
	/**
	 * 判断UVF前置约束是否包含对某变量的约束
	 * @param var
	 * @return
	 */
	public boolean contains(VariableNameDeclaration var) {
		if (var == null) {
			return false;
		}
		return varList.containsKey(var); 
	}
	/**
	 * 获取前置条件中某指定变量的初始化约束
	 * @param var
	 * @return
	 */
	public UVF_PInfo getUVF_PInfo(VariableNameDeclaration var) {
		return varList.get(var);
	}
	/**
	 * 判断该UVF前置约束是否为空
	 * @return
	 */
	public boolean isEmpty() {
		return varList.size() == 0;
	}
	/**
	 * 获取含有前置约束的变量集合
	 * @return
	 */
	public Set<VariableNameDeclaration> getUVF_PVariables() {
		return varList.keySet();
	}
	/**
	 * 得到当前相应变量var的type
	 */
	public UVF_PType getUVF_PType(VariableNameDeclaration var) {
		return getUVF_PInfo(var).type;
	}
	/**
	 * 得到当前相应变量var的paramIndex
	 */
	public int getUVF_PIndex(VariableNameDeclaration var) {
		return getUVF_PInfo(var).paramIndex;
	}
	@Override
	public String toString() {
		return "MethodUVF_PPreCondition [varList=" + varList + ", name=" + name
				+ ", isEmpty()=" + isEmpty() + ", getUVF_PVariables()="
				+ getUVF_PVariables() + ", getName()=" + getName()
				+ ", toString()=" + super.toString() + ", getClass()="
				+ getClass() + ", hashCode()=" + hashCode() + "]";
	}
	
}
