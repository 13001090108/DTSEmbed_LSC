package softtest.summary.lib.c;

import softtest.ast.c.SimpleNode;
import softtest.summary.c.MethodFeatureType;
import softtest.summary.c.MethodSummary;

/**
 * Some safety patterns need some description or IP rank for the functions.
 * This class is to record such information. It extends LibMethodDesp.
 * @author Yao Xinhong
 *
 */
public abstract class LibMethodDespComplement extends LibMethodDesp {
 
	String description;
	String rank;
	
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
	
	public LibMethodDespComplement(MethodFeatureType type, Object value) {
		super(type, value);
	}
	
	@Override
	public abstract void createFeature(String libName, SimpleNode node,
			MethodSummary mtSummary) ;
}
