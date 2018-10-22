package softtest.summary.lib.c;

import softtest.ast.c.SimpleNode;
import softtest.summary.c.MethodAPIAbuseFeature;
import softtest.summary.c.MethodFeatureType;
import softtest.summary.c.MethodSummary;

/**
 * <p>
 * The API abuse feature loaded from the apiabuse_summary.xml and add itself into the summary. 
 * </p>
 * 
 * @author liuyan
 *
 */
public class LibMethodDespAPIAbuse extends LibMethodDespComplement {

	public LibMethodDespAPIAbuse(MethodFeatureType type, String description, String rank) {
		super(type, null);
		this.description = description;
		this.rank = rank;
	}
	
	@Override
	public void createFeature(String libName, SimpleNode node,
			MethodSummary mtSummary) {
		MethodAPIAbuseFeature apiAbuseFeature = new MethodAPIAbuseFeature();
		
		apiAbuseFeature.setDescription(description);
		apiAbuseFeature.setRank(rank);
		
		mtSummary.addSideEffect(apiAbuseFeature);
	}
}
