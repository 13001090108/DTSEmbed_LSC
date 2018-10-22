package softtest.symboltable.c.Type;

public class CType_Unkown extends CType {
	
	public CType_Unkown(String Name) {
		super();
		this.name = Name;
	}

	@Override
	public int getSize() {
		return softtest.config.c.Config.INT_SIZE;
	}
}
