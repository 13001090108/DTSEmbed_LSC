package softtest.symboltable.c;

import java.util.ArrayList;

import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.symbolic.Factor;
import softtest.interpro.c.Variable;
import softtest.symboltable.c.Type.*;

public class VariableNameDeclaration extends AbstractNameDeclaration {
	/* whether the variable is static*/
	//若为复杂成员，则在此出将成员声明增加
	//add by zhouhb
	public ArrayList<VariableNameDeclaration> mems = new ArrayList<VariableNameDeclaration>();
	
	//对于指针变量int *p除了p以外，为了支持区间运算会产生*p变量，为了区分做标签处理
	private boolean isGen =false;
	
	private boolean isStatic = false;
	
	private boolean isExtern = false;
	
	private boolean isEnum = false;
	
	/* the parameter index If the variable is a parameter of a function*/
	private int paramIndex = -1;
	
	/**zys:获取变量声明时的初始值，以此初始化符号的值域；如果无初始值或初始赋值为一复杂表达式，则该属性为空*/
	private Variable variable;
	
	//父变量，表示成员变量与复杂结构变量的 成员父子关系
	//add by dongyk
	private NameDeclaration fatherVariable=null;

	public NameDeclaration getFatherVariable() {
		return fatherVariable;
	}

	public void setFatherVariable(NameDeclaration fatherDecl) {
		this.fatherVariable = fatherDecl;
	}
	
	
	//add by zhouhb
	//2011.4.25
	public VariableNameDeclaration(String fileName,Scope scope,String image,SimpleNode node){
		super(fileName,scope,image,node);
	}
	
	public VariableNameDeclaration(ASTPostfixExpression node){
		super(node);
	}
	//end by zhouhb
	
	public VariableNameDeclaration(ASTUnaryExpression node){
		super(node);
	}
	//end by dongyk
	
	public VariableNameDeclaration(ASTDirectDeclarator node) {
		super(node);
	}

	public VariableNameDeclaration(ASTEnumerator node) {
		super(node);
		isEnum=true;
	}
	
	public VariableNameDeclaration(ASTParameterDeclaration node)
	{
		super(node);
	}
	
	@Override
	//modified by zhouhb
	//2011.5.5
	public boolean equals(Object o) {
		if(Config.Field){
			VariableNameDeclaration n = (VariableNameDeclaration) o;
			if(node==null){
				return true;
			}else if(n==null||n.node==null)
			{
				return true;
			}else{
				return n.node.equals(node);
			}
		}else{
			VariableNameDeclaration n = (VariableNameDeclaration) o;
			return n.node.equals(node);
		}
	}


	@Override
	//modified by zhouhb
	//2011.5.5
	public int hashCode() {
		if(Config.Field){
			//add by zhouhb
			//2011.5.5
			//当一个节点上关联多个结构体成员声明时，或者多级指针声明时，不能再用节点的image作为hashCode
			return this.getImage().hashCode();
		}else{
			return node.getImage().hashCode();
		}
	}

	public boolean isPrimitiveType() {
		return this.isPrimitiveType(this.type);
	}

	private boolean isPrimitiveType(CType t) {
		return t instanceof CType_BaseType || (t instanceof CType_Qualified && isPrimitiveType(((CType_Qualified) t)
						.getOriginaltype()));
	}

	public boolean isArray() {
		return isArray(this.type);
	}

	private boolean isArray(CType t) {
		return t instanceof CType_Array
				|| (t instanceof CType_Qualified && isArray(((CType_Qualified) t)
						.getOriginaltype()));
	}

	public String getTypeImage() {
		if(type!=null)
			return type.toString();
		return null;
	}

	public int getArrayDepth() {
		if (isArray())
			return -1;
		int deep = 0;
		CType t = this.type;
		while (t instanceof CType_Qualified || t instanceof CType_Array) {
			if (t instanceof CType_Array) {
				deep++;
				t = ((CType_Array) t).getOriginaltype();
			} else
				t = ((CType_Qualified) t).getOriginaltype();
		}
		return deep;

	}
	
	public boolean isStatic() {
		return isStatic;
	}

	public void setStatic(boolean isStatic) {
		this.isStatic = isStatic;
	}
	
	public boolean isExtern () {
		return isExtern;
	}

	public void setExtern (boolean isExtern) {
		this.isExtern = isExtern;
	}

	public boolean isEnum() {
		return isEnum;
	}

	public void setEnum(boolean isEnum) {
		this.isEnum = isEnum;
	}

	public Variable getVariable() {
		return variable;
	}

	public void setVariable(Variable variable) {
		this.variable = variable;
	}
	
	public boolean isParam() {
		return paramIndex != -1;
	}

	public int getParamIndex() {
		return paramIndex;
	}

	public void setParamIndex(int paramIndex) {
		this.paramIndex = paramIndex;
	}
	/** 变量初始化域 */
	private Domain domain = null;

	/** 设置初始域 */
	public void setDomain(Domain domain) {
		this.domain = domain;
	}
	/** 获得初始域 */
	public Domain getDomain() {
		if(domain==null)	
			return null;
		else
			try{
				return (domain).clone();}
			catch (CloneNotSupportedException e) {
				e.printStackTrace();
				return null;
			}
	}
	
	public boolean isGen() {
		return isGen;
	}

	public void setGen(boolean isGen) {
		this.isGen = isGen;
	}
}
