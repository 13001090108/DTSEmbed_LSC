package softtest.summary.lib.c;

import softtest.ast.c.SimpleNode;
import softtest.rules.gcc.fault.BO.*;
import softtest.summary.c.MethodFeatureType;
import softtest.summary.c.MethodSummary;
import softtest.summary.gcc.fault.MethodBOPreCondition;

public class LibMethodDespBo extends LibMethodDesp {
	private String srcIndex;
	private String bufIndex;
	private String limitLen;
	private BOType subtype;
	private boolean needNull;
	
	public LibMethodDespBo(MethodFeatureType type, Object value) {
		super(type, value);
	}

	public LibMethodDespBo(MethodFeatureType type, String subtype, String bufIndex, String srcIndex, String limitLen, boolean needNull) {
		super(type, null);
		this.srcIndex = srcIndex;
		this.bufIndex = bufIndex;
		this.limitLen = limitLen;
		this.needNull = needNull;
		
		if (subtype.equals("BUFFERCOPY")) {
			this.subtype = BOType.BUFFERCOPY;
		}
	}

	@Override
	public void createFeature(String libName, SimpleNode node, MethodSummary mtSummary) {
		MethodBOPreCondition boPrecondition = new MethodBOPreCondition();
		//记录XML中各feature的属性
		
		boPrecondition.setSubtype(subtype);
		boPrecondition.setBufIndex((new Integer(bufIndex)).intValue());
		boPrecondition.setSrcIndex((new Integer(srcIndex)).intValue());
		boPrecondition.setLimitLen((new Integer(limitLen)).intValue());
		boPrecondition.setNeedNull(needNull);
		
		mtSummary.addPreCondition(boPrecondition);
		
	}
	

}
