package softtest.summary.lib.c;


import softtest.ast.c.SimpleNode;
import softtest.summary.c.MethodFeatureType;
import softtest.summary.c.MethodSummary;

/**
 * <p>
 * The reserved MFD which load from the XML, no feature is added into the summary
 * </p>
 * 
 * @author Qi Peng
 *
 */
public class LibMethodDespReserved extends LibMethodDesp {

	public LibMethodDespReserved(MethodFeatureType type, Object value) {
		super(type, value);
	}

	public void createFeature(String libName, SimpleNode node, MethodSummary mtSummary) {	
	}

}
