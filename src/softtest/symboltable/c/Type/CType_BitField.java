package softtest.symboltable.c.Type;

public class CType_BitField extends CType {
	public int bitfield = -1;
	public CType originaltype;

	public CType_BitField() {
		name = "bitfield";
	}

	public CType getOriginaltype() {
		return originaltype;
	}

	public void setOriginaltype(CType originaltype) {
		this.originaltype = originaltype;
	}
	
	public int getBitfield() {
		return bitfield;
	}

	public void setBitfield(int bitfield) {
		this.bitfield = bitfield;
	}

	@Override
	public String toString() {
		return originaltype.toString() + ":" + name + "_" + bitfield;
	}

	@Override
	public int getSize() {
		return (bitfield-1)/8+1;
	}
}
