package softtest.symboltable.c.Type;

//add by zhouhb
//描述分配类型信息

public class CType_AllocType extends CType{
	public static final CType_AllocType heapType = new CType_AllocType("Heap");
	public static final CType_AllocType stackType = new CType_AllocType("Stack");
	public static final CType_AllocType staticType=new CType_AllocType("Static");
	public static final CType_AllocType Null=new CType_AllocType("Null");
	public static final CType_AllocType NotNull=new CType_AllocType("NotNull");
//	public static final CType_AllocType Unkown=new CType_AllocType("Unkown");
//	public static final CType_AllocType Empty=new CType_AllocType("Empty");
	
	public CType_AllocType() {
	}
	public CType_AllocType(String name) 
	{
		this.name = name;
	}
	public boolean isHeap(){
		if(this.name.equals("Heap"))
			return true;
		else 
			return false;
	}	public boolean isStack(){
		if(this.name.equals("Stack"))
			return true;
		else 
			return false;
	}
	public boolean isNULL(){
		if(this.name.equals("Null"))
			return true;
		else 
			return false;
	}
	public boolean isConst(){
		if(this.name.equals("Static"))
			return true;
		else 
			return false;
	}
    public static CType_AllocType getAllocType(String name) {
		
		if (name.equals("Heap")) {
			return heapType;
		} else if (name.equals("Stack")) {
			return stackType;
		} else if(name.equals("Static")){
			return staticType;
		}else if(name.equals("Null")){
			return Null;
		}else if(name.equals("NotNull")){
			return NotNull;
//		}else if(name.equals("Unkown")){
//			return Unkown;
//		}else if(name.equals("Empty")){
//			return Empty;
		}else{
			CType_AllocType type = new CType_AllocType();
			type.setName(name);
			return type;
		}
	}
    
    @Override
	//这里的size没有意义，只是为了实现抽象方法
    public int getSize(){
    	return 1;
    }
}
