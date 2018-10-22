package softtest.summary.c;
/**
 *  @author liuyan
 */

public class MethodFeatureComplement extends MethodFeature {
	
	protected String description;
	protected String rank;
	
	public String getDescription() {
		return description;
	}

	public void setDescription(String description) {
		this.description = description;
	}

	public String getRank() {
		return rank;
	}

	public void setRank(String rank) {
		this.rank = rank;
	}

	public MethodFeatureComplement (String name) {
		super(name);
	}
}
