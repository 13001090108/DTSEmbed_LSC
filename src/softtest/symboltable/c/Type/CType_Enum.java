package softtest.symboltable.c.Type;

public class CType_Enum extends CType {
	public int enumLong;
	
	public void setValue(int num) {
		this.enumLong=num;
	}
	
	public int getValue() {
		return this.enumLong;
	}
	
	public CType_Enum(String name) {
		super(name);
	}
	
	@Override
	public String toString() {
		return "enum " + name;
	}

	@Override
	public int getSize() {
		return softtest.config.c.Config.INT_SIZE;
	}
}
