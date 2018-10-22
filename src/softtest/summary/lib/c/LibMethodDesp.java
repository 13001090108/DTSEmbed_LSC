package softtest.summary.lib.c;

import softtest.ast.c.SimpleNode;
import softtest.summary.c.MethodFeatureType;
import softtest.summary.c.MethodSummary;

/**
 * <p>
 * The Lib MFD(method feature description) that describe the C/C++ lib methods, which loads from the XML.
 * This is an abstract class for user custom feature, anyone can inherit to create new lib feature
 * </p>
 * @author Qi Peng
 *
 */
public abstract class LibMethodDesp {
	
	/**
	 * <p>The type of this feature</p>
	 */
	MethodFeatureType type;
	
	/**
	 * <p>The default value of this feature</p>
	 */
	Object value;

	public LibMethodDesp(MethodFeatureType type, Object value) {
		this.type = type;
		this.value = value;
	}
	
	/**
	 * Gets the type of the lib method feature
	 * 
	 * @return
	 */
	public MethodFeatureType getType() {
		return type;
	}

	/**
	 * Gets the value of the lib method feature
	 * @return
	 */
	public Object getValue() {
		return value;
	}
	
	/**
	 * Create the method feature from the AST root and add the feature into the method summary
	 * Convert the MFD into method Summary
	 * 
	 * @param libName the library name which contains this method, in C/C++ for include file name
	 * @param node the AST root node for this method
	 * @param mtSummary the method summary for this method
	 */
	public abstract void createFeature(String libName, SimpleNode node, MethodSummary mtSummary);

	@Override
	public String toString() {
		StringBuffer sb=new StringBuffer();
		if(type!=null)
			sb.append(type.toString());
		if(value!=null)
			sb.append(value.toString());
		return sb.toString();
	}
}
