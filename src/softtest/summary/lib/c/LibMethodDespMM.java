package softtest.summary.lib.c;

import softtest.ast.c.SimpleNode;
import softtest.summary.c.MethodFeatureType;
import softtest.summary.c.MethodSummary;
import softtest.summary.gcc.fault.MethodMMFeature0;

public class LibMethodDespMM extends LibMethodDesp
{
	private String subType;
	private String paramIndex;
	
	public LibMethodDespMM(MethodFeatureType type, String stype, String pIndex)
	{
		super(type,null);
		this.subType = stype;
		this.paramIndex = pIndex;
		
	}
	
	@Override
	public void createFeature(String libName, SimpleNode node,MethodSummary mtSummary)
	{
		MethodMMFeature0 mmFeature = new MethodMMFeature0();
		
		try
		{
			int index = Integer.parseInt(paramIndex);
			int sub = Integer.parseInt(subType);
			
			switch(sub)
			{
				case 0:
					mmFeature.setMMRelease(true);
					mmFeature.setMMAllocate(false);
					break;
				case 1:
					mmFeature.setMMAllocate(true);
					mmFeature.setMMRelease(false);
					break;
				default:
					break;
			}
			
			mmFeature.setParamIndex(index);
		}
		catch(Exception ex)
		{
			mmFeature.setParamIndex(-1);
			mmFeature.setMMAllocate(false);
			mmFeature.setMMRelease(false);
		}
		
		mtSummary.addSideEffect(mmFeature);
		
	}

}
