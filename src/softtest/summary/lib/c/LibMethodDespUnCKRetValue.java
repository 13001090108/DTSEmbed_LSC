package softtest.summary.lib.c;

import softtest.ast.c.SimpleNode;
import softtest.summary.c.MethodFeatureType;
import softtest.summary.c.MethodSummary;
import softtest.summary.c.MethodUnCKRetValuePostCondition;

/**
 * <p>
 * The feature for un-check return value of the functions loaded from XML, and add itself to the summary as PostCondition.
 * </p>
 * @author liuyan
 *
 */
public class LibMethodDespUnCKRetValue extends LibMethodDespComplement {

	public LibMethodDespUnCKRetValue(MethodFeatureType type, String description, String rank) {
		super(type, null);
		this.description = description;
		this.rank = rank;
	}
	@Override
	public void createFeature(String libName, SimpleNode node,
			MethodSummary mtSummary) {
		MethodUnCKRetValuePostCondition unckRetValuePostCondition = new MethodUnCKRetValuePostCondition();
		unckRetValuePostCondition.setDescription(description);
		unckRetValuePostCondition.setRank(rank);
		
		mtSummary.addPostCondition(unckRetValuePostCondition);
	}
}
