package softtest.symboltable.c.Type;

import javax.sql.rowset.JdbcRowSet;

import softtest.domain.c.interval.DomainType;
import softtest.symboltable.c.Scope;

//基本类型
public abstract class CType implements java.io.Serializable{
	protected String name = "";

	public CType() {
		
	}
	
	public CType(String name) {
		this.name = name;
	}
	public void setName(String name) {
		this.name = name;
	}

	public String getName() {
		return name;
	}
	
	public boolean isPointType(){
		return false;
	}
	
	public boolean isArrayType(){
		return false;
	}
	
	public boolean isBasicType(){
		return false;
	}
	
	public boolean isClassType(){
		return false;
	}
	
	public boolean isIntegerType(){
		return false;
	}
	//add by zhouhb
	//2010.3.15
	public boolean isUnsignedType(){
		if(this.toString().contains("unsigned")){
			return true;
		}
		else
			return false;
	}
	
	/**
	 * 确定两个类型是否等价
	 * 
	 * @param o
	 * @return
	 */
	public boolean equalType(Object o) {
		if ((o == null) || !(o instanceof CType)) {
			return false;
		}
		if (this == o) {
			return true;
		}
		
		CType type1 = getNormalType();
		CType type2 = ((CType)o).getNormalType();

		if (!type1.toString().equals(type2.toString())) {
			return false;
		}
		return true;
	}
	@Override
	public boolean equals(Object o) {
		if ((o == null) || !(o instanceof CType)) {
			return false;
		}
		if (this == o) {
			return true;
		}
		
		CType type1 = getNormalType();
		CType type2 = ((CType)o).getNormalType();

		if (!type1.toString().equals(type2.toString())) {
			return false;
		}
		return true;
	}
	
	@Override
	public int hashCode()
	{
		return toString().hashCode();
	}
	
	@Override
	public String toString() {
		return name; 
	}
	
	public static boolean isPrimitiveType(CType t) {
		if (t instanceof CType_Pointer || t instanceof CType_Struct || t instanceof CType_Union) {
			return false;
		}
		return t instanceof CType_BaseType || (t instanceof CType_Qualified && isPrimitiveType(((CType_Qualified) t).getOriginaltype()));
	}
	
	// 获取某类型指向的原始对象类型
	// 可用于Pointer, Typedef, Address, Array
	
	public static CType getOrignType(CType type) {
		CType temp = type;
		while ((temp instanceof CType_Typedef)||(temp instanceof CType_Pointer)
				||(temp instanceof CType_Qualified) ||(temp instanceof CType_Array) ){
			if (temp instanceof CType_Typedef){
    			CType_Typedef def=(CType_Typedef)temp;
    			temp = def.getOriginaltype();
    			//判断如果是指针类型就退出
    			//ytang add
    			if(temp instanceof CType_Pointer){
    				break;
    			}
    		} else if (temp instanceof CType_Pointer) {
    			CType_Pointer pointer=(CType_Pointer)temp;
    			temp = pointer.getOriginaltype();
			} else if (temp instanceof CType_Qualified) {
				CType_Qualified pointer=(CType_Qualified)temp;
    			temp = pointer.getOriginaltype();
			} else if (temp instanceof CType_Array) {
				CType_Array array = (CType_Array)temp;
    			temp = array.getOriginaltype();
			}
		}
		return temp;
	}
		
	// 获取某类型指向的原始对象类型
	// 可用于Pointer, Typedef, Address, Array
	public static CType getOneOrignType(CType type) {
		CType temp = type;
		
			if (temp instanceof CType_Typedef){
    			CType_Typedef def=(CType_Typedef)temp;
    			temp = def.getOriginaltype();
    		} else if (temp instanceof CType_Pointer) {
    			CType_Pointer pointer=(CType_Pointer)temp;
    			temp = pointer.getOriginaltype();
			} else if (temp instanceof CType_Qualified) {
				CType_Qualified pointer=(CType_Qualified)temp;
    			temp = pointer.getOriginaltype();
			} else if (temp instanceof CType_Array) {
				CType_Array array = (CType_Array)temp;
    			temp = array.getOriginaltype();
			}
		
		return temp;
	}
	
	// 获取某类型指向的上层对象类型
	//add by zhouhb 2010/8/24
	public static CType getNextType(CType type) {
		CType temp = type;
			if (temp instanceof CType_Typedef){
    			CType_Typedef def=(CType_Typedef)temp;
    			temp = def.getOriginaltype();
    		} else if (temp instanceof CType_Pointer) {
    			CType_Pointer pointer=(CType_Pointer)temp;
    			temp = pointer.getOriginaltype();
			} else if (temp instanceof CType_Qualified) {
				CType_Qualified pointer=(CType_Qualified)temp;
    			temp = pointer.getOriginaltype();
			} else if (temp instanceof CType_Array) {
				CType_Array array = (CType_Array)temp;
    			temp = array.getOriginaltype();
			}
		return temp;
	}
	
	// 作用等价于GetOrignType，用于对象，而不是静态方法
	public CType getSimpleType() {
		return this;
	}
	
	// 不考虑typedef 和qualified类型，用于判读两个类型是否相等
	public CType getNormalType() {
		CType temp = this;
		while ((temp instanceof CType_Typedef)||(temp instanceof CType_Qualified)){
			if (temp instanceof CType_Typedef) {
				temp = ((CType_Typedef)temp).getOriginaltype(); 
			} else if (temp instanceof CType_Qualified) {
				temp = ((CType_Qualified)temp).getOriginaltype();
			}
		}
		return temp;
	}
	
	public static boolean setOrignType(CType type, CType origin) {
		CType temp=null;
		if(type instanceof CType_Qualified ){
			CType_Qualified d=(CType_Qualified)type;
			temp=d.getOriginaltype();
			if(temp==null){
				d.setOriginaltype(origin);
				return true;
			}else if(temp instanceof CType_Qualified||temp instanceof CType_Function|| temp instanceof CType_AbstPointer){
				return setOrignType(temp,origin);
			}else{
				return false;
			}
		}
		
		if(type instanceof CType_Function ){
			CType_Function d=(CType_Function)type;
			temp=d.getOriginaltype();
			if(temp==null){
				d.setOriginaltype(origin);
				return true;
			}else if(temp instanceof CType_Qualified||temp instanceof CType_Function|| temp instanceof CType_AbstPointer){
				return setOrignType(temp,origin);
			}else{
				return false;
			}
		}
		
		if(type instanceof CType_BitField ){
			CType_BitField d=(CType_BitField)type;
			temp=d.getOriginaltype();
			if(temp==null){
				d.setOriginaltype(origin);
				return true;
			}else{
				return false;
			}
		}
		
		if(type instanceof CType_AbstPointer ){
			CType_AbstPointer d=(CType_AbstPointer)type;
			temp=d.getOriginaltype();
			if(temp==null){
				d.setOriginaltype(origin);
				return true;
			}else if(temp instanceof CType_Qualified||temp instanceof CType_Function|| temp instanceof CType_AbstPointer){
				return setOrignType(temp,origin);
			}else{
				return false;
			}
		}
		return false;
	}
			
	public abstract int getSize();
	
	public boolean isString() {
		if (this instanceof CType_AbstPointer) {
			return getOrignType(this) == CType_BaseType.charType;
		}
		return false;
 	}

	public void calClassSize(Scope declscope) {
	}
	
	public DomainType getDomainType(){
		if(this.isPointType()){
			return DomainType.POINTER;
		}else if(!this.isIntegerType()){
			return DomainType.DOUBLE;
		}else{
			return DomainType.INTEGER;
		}
	}
	
} 

