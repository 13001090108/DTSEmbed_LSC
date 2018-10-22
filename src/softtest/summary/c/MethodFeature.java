package softtest.summary.c;

public abstract class MethodFeature {
	
	protected String name;
	
	public MethodFeature(String name) {
		this.name = name;
	}

	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}

	@Override
	public String toString() {
		return name;
	}
}
