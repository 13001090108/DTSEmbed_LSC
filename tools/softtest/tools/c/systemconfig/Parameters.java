package softtest.tools.c.systemconfig;

public class Parameters {
	String name;
	String description;
	StringBuffer value;
	public Parameters(String name, String description, StringBuffer value){
		this.name = name;
		this.description = description;
		this.value = value;
	}
}
