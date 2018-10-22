package softtest.summary.gcc.fault;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import softtest.interpro.c.Variable;
import softtest.rules.gcc.fault.BO.BOType;
import softtest.summary.c.MethodFeature;
import softtest.symboltable.c.VariableNameDeclaration;

/**
 * BO前置条件函数摘要的实体类
 *
 */
public class MethodBOPreCondition extends MethodFeature {
	//使用内部类存储BO变量对应的信息：对应区间，错误描述信息
	class BOInfo {
		long size;
		String desbuf;
		String desmet;
		boolean flag;
		public BOInfo(long size, String desbuf,String desmet, boolean flag) {
			this.size = size;
			this.desbuf = desbuf;
			this.desmet = desmet;
			this.flag = flag;
		}
	}
	private Map<Variable, BOInfo> varList;
	
	//以下四个属性仅对库函数有意义
	private BOType subtype;//当前BO函数摘要类型，有BUFFERCOPY等
	private int bufIndex;//目的缓冲区位置序号 如strcpy(buf, src),此时的值为0
	private int srcIndex;//源缓冲区位置序号
	private int limitLen;//限制复制长度参数的序号，如strncpy(buf, src, n);此时为2，对于其他没有限制长度的，值均为-1
	private boolean needNull;//判断是否需要为该函数预留一个字节保存'\0'

	public final static String METHOD_BO_PRECONDITION = "METHOD_BO_PRECONDITION";
	
	
	public MethodBOPreCondition() {
		super(METHOD_BO_PRECONDITION);
		varList = new HashMap<Variable, BOInfo>();
	}
	
	/**
	 * 添加指定变量及约束信息到前置约束中
	 * @param var
	 * @param des
	 */
	public void addVariable(Variable var,long size, String desbuf, String desmet, boolean flag) {
		varList.put(var, new BOInfo(size, desbuf, desmet, flag));
	}
	/**
	 * 判断BO前置约束是否包含对某变量的约束
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
	
	public Set<Variable> getBOVariables() {
		return varList.keySet();
	}
	/**
	 * 获取前置条件中某指定变量的区间约束
	 * @param var
	 * @return
	 */
	public BOInfo getBoInfo(Variable var) {
		return varList.get(var);
	}
	/**
	 * 判断该BO前置约束是否为空
	 * @return
	 */
	public boolean isEmpty() {
		return varList.size() == 0;
	}
	//这个有必要吗？
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

	public int getBufIndex() {
		return bufIndex;
	}

	public void setBufIndex(int bufIndex) {
		this.bufIndex = bufIndex;
	}

	public int getSrcIndex() {
		return srcIndex;
	}

	public void setSrcIndex(int srcIndex) {
		this.srcIndex = srcIndex;
	}

	public int getLimitLen() {
		return limitLen;
	}

	public void setLimitLen(int limitLen) {
		this.limitLen = limitLen;
	}

	public BOType getSubtype() {
		return subtype;
	}

	public void setSubtype(BOType subtype) {
		this.subtype = subtype;
	}

	public boolean isNeedNull() {
		return needNull;
	}

	public void setNeedNull(boolean needNull) {
		this.needNull = needNull;
	}

	/**
	 * 得到当前相应变量var的区间值
	 * @param var
	 * @return
	 */
	public long getsize(Variable var) {
		return varList.get(var).size;
	}
	
	/**
	 * 得到当前相应变量是限制源缓冲区还是目标缓冲区的标识
	 * @param var
	 */
	public boolean getflag(Variable var){
		return varList.get(var).flag;
	}
	/**
	 * 得到前置条件关于目标缓冲区的描述
	 */
	public String getDespbuf(Variable var){
		return varList.get(var).desbuf;
	}
	public String getDespmet(Variable var){
		return varList.get(var).desmet;
	}
}


