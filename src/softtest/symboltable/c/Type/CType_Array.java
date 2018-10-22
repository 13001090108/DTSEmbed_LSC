package softtest.symboltable.c.Type;

//数组类型
public class CType_Array extends CType_AbstPointer {
	
	// int a[]
	private boolean fixed = false;
	private long dim_size = -1;

	public CType_Array() {
		name = "array";
	}
	public CType_Array(CType origin) {
		super(origin);
		name = "array";
	}

	public long getDimSize() {
		return dim_size;
	}

	public void setDimSize(long size) {
		dim_size = size;
	}
	
	@Override
	public String toString() {
		if (fixed) {
			return "["+dim_size+"]"+originaltype;
		} else {
			return "[]"+originaltype;
		}
	}
	
	@Override
	public int getSize() {
		if (originaltype == null) {
			return (int)dim_size * 4;
		}
		int temp = (int)dim_size;
		if (temp <= 0) {
			temp = 1;
		}
		return temp*originaltype.getSize();
	}
	public boolean isFixed() {
		return fixed;
	}
	public void setFixed(boolean fixed) {
		this.fixed = fixed;
	}

	@Override
	public boolean isArrayType(){
		return true;
	}
	
	//为了限制域敏感分析数组的成员数量，提供此函数获取成员数量
	//add by zhouhb
	//2011.10.12
	public int getMemNum() {
		return this.getSize()/4;
	}
	//end by zhouhb
	
}
