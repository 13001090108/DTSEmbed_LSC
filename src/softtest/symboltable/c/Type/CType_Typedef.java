package softtest.symboltable.c.Type;

public class CType_Typedef extends CType {
	public CType originaltype;

	public CType_Typedef(String name) {
		super(name);
	}
	
	public CType getOriginaltype() {
		return originaltype;
	}

	public void setOriginaltype(CType originalType) {
		originaltype = originalType;
	}

	@Override
	public boolean isClassType() {
		if (originaltype == null) {
			return false;
		}
		return originaltype.isClassType();
	}
	
	@Override
	public boolean isBasicType() {
		if (originaltype == null) {
			return false;
		}
		return originaltype.isBasicType();
	}
	
	@Override
	public boolean isPointType() {
		if (originaltype == null) {
			return false;
		}
		return originaltype.isPointType();
	}
	
	@Override
	public boolean isIntegerType(){
		if (originaltype == null) {
			return false;
		}
		return originaltype.isIntegerType();
	}
	
	@Override
	public boolean isArrayType(){
		if (originaltype == null) {
			return false;
		}
		return originaltype.isArrayType();
	}
	
	@Override
	public CType getSimpleType() {
		if (originaltype != null) {
			return originaltype.getSimpleType();
		}
		return null;
	}
	
	@Override
	public int getSize() {
		if (originaltype == null) {
			return softtest.config.c.Config.INT_SIZE;
		}
		return originaltype.getSize();
	}
	@Override
	public String toString() {
		//liuli：2010.8.17 针对typedef int (func) (int *i);这种类型的声明造成的空指针，暂时跳过
		if(originaltype == null)
			return null;
		return name + ":" + originaltype.toString();
	}
}