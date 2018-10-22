package softtest.symboltable.c.Type;

public abstract class CType_AbstPointer extends CType {

	protected CType originaltype;
	
	public CType_AbstPointer() {
		
	}
	
	public CType_AbstPointer(CType originalType) {
		this.originaltype = originalType;
	}

	public CType getOriginaltype() {
		return originaltype;
	}

	//add by zhouhb
	//如果originaltype为typedef，则继续追踪到具体类型
	public CType getDeepOriginaltype() {
		if(originaltype instanceof CType_Typedef){
			return ((CType_Typedef) originaltype).getOriginaltype();
		}else
			return originaltype;
	}
	public void setOriginaltype(CType originalType) {
		this.originaltype = originalType;
	}
	
	@Override
	public boolean isPointType() {
		return true;
	}
}
