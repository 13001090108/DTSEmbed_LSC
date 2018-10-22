package softtest.symboltable.c.Type;

public class CType_Pointer extends CType_AbstPointer {
	
	public static final CType_Pointer CPPString = new CType_Pointer(CType_BaseType.charType);
	public static final CType_Pointer VOID = new CType_Pointer(CType_BaseType.voidType);

	//计算指针级数
	//add by zhouhb
	//2011.5.17
	private int rank=1;
	public int getRank(){
		CType temp=this.getOriginaltype();
		while(temp instanceof CType_Pointer){
			rank++;
			temp=((CType_Pointer)temp).getOriginaltype();
		}
		return rank;
	}
	//end by zhouhb
	
	private CType_Pointer(CType originalType) {
		super(originalType);
		name = "pointer"; 
	}
	
	public CType_Pointer() {
		name = "pointer";
	}
	
	@Override
	public boolean isPointType(){
		return true;
	}
	
	@Override
	public String toString() {
		if(originaltype != null)
			return "*" + originaltype.toString();
		else
			return "*";
	}
	//int32
	@Override
	public int getSize() {
		return 4;
	}
}
