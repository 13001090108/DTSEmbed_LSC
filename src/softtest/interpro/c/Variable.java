package softtest.interpro.c;

import java.io.Serializable;

import softtest.symboltable.c.*;
import softtest.symboltable.c.Type.*;

/**
 * 
 * 全局独立的变量信息，可以描述函数参数变量，成员变量，以及全局变量
 * 由于局部变量在函数作用域退出之后，失去作用，因此并不记录其信息
 *
 */
public class Variable implements Serializable {

	/**每一个变量的真实值 */
	private Object value;
	/**
	 * 每一个变量声明都与一个Variable关联，记录变量声明时的初始化赋值信息
	 */
	public Variable(String name,Object value)
	{
		this.name=name;
		this.value=value;
	}
	/**
	 * 变量对应的名字
	 */
	private String name;
	
	/**
	 * 变量的作用域，分三种：函数（函数的作用域），类，全局
	 */
	private ScopeType scopeType;
	
	private String scopeName;
	
	/**
	 * 变量的类型
	 */
	private CType type;
	
	/**
	 * 形参变量对应的函数列表的序号，只有在该变量为函数参数时候才有意义
	 */
	private int paramIndex = -1;
	
	public Variable(ScopeType scopeType, String name, CType type) {
		this.scopeType = scopeType;
		this.name = name;
		this.type = type;
	}
	 
	/**
	 * 根据一个变量的本地分析符号表声明产生其对应的全局独立的与函数摘要关联的变量描述
	 * @param decl
	 * @return
	 */
	public static Variable getVariable(VariableNameDeclaration decl) {
		if (decl == null) {
			return null;
		}
		if (decl.getVariable() != null) {
			return decl.getVariable();
		}
		Scope scope = decl.getScope();
		Variable var = null;
		if (scope instanceof MethodScope && decl.isParam()) {
			var = new Variable(ScopeType.METHOD_SCOPE, decl.getImage(), decl.getType());
			var.setParamIndex(decl.getParamIndex());
			var.setScopeName(decl.getFileName());
			decl.setVariable(var);
		} else if (scope instanceof ClassScope) {
			var = new Variable(ScopeType.CLASS_SCOPE, decl.getImage(), decl.getType());
			var.setScopeName(scope.getName());
			decl.setVariable(var);
		} else if (scope instanceof SourceFileScope) {
			var = new Variable(ScopeType.INTER_SCOPE, decl.getImage(), decl.getType());
			var.setScopeName(decl.getFileName());
			decl.setVariable(var);
		}
		return var;
	}
	
	
	@Override
	public boolean equals(Object o) {
		if ((o == null) ||  !(o instanceof Variable)) {
			return false;
		}
		if (this == o) {
			return true;
		}
		Variable var = (Variable)o;
		if (!this.name.equals(var.getName())) {
			return false;
		}
		if (this.scopeType != var.getScopeType()) {
			return false;
		}
		if (this.scopeName==null||!this.scopeName.equals(var.getScopeName())) {
			return false;
		}
		if (this.getParamIndex() != var.getParamIndex()) {
			return false;
		}
		return true;
	}
	
	@Override
	public int hashCode() {
		int ret = 0;
		if (scopeName != null) {
			ret = name.hashCode() + scopeName.hashCode() + this.paramIndex;
		} else {
			ret = name.hashCode() + this.paramIndex;
		}
		return ret;
	}
	
	
	// getters and setters
	public String getName() {
		return name;
	}

	public int getParamIndex() {
		return paramIndex;
	}

	public ScopeType getScopeType() {
		return scopeType;
	}

	public CType getType() {
		return type;
	}

	public boolean isParam() {
		return this.paramIndex != -1;
	}
	public void setParamIndex(int paramIndex) {
		this.paramIndex = paramIndex;
	}

	public String getScopeName() {
		return scopeName;
	}

	public void setScopeName(String scopeName) {
		this.scopeName = scopeName;
	}
	
	@Override
	public String toString() {
		return name;
	}

	public Object getValue()
	{
		return value;
	}

	public void setValue(Object value)
	{
		this.value = value;
	}
}
