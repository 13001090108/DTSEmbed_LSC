package softtest.summary.gcc.fault;

import java.io.FileInputStream;
import java.io.InputStream;
import java.util.Properties;

import softtest.summary.c.MethodFeature;

public class MethodMMFeature0 extends MethodFeature
{
	/**特别需要注意的是这里要用variable 而不能用variableNameDeclaration*/
	/**与变量无关吧*/
	/**是不是要再加一个属性 表明是释放的函数的第几个参数*/
	
	public final static String METHOD_MM_FEATURE = "METHOD_MLF_FEATURE";
	
	private boolean isMMAllocate = false;
	private boolean isMMRelease = false;
	
	private String allocatedMethod = null;
	
	private int paramIndex = -1;

	public MethodMMFeature0()
	{
		super(METHOD_MM_FEATURE);
	}
	
	public int getParamIndex()
	{
		return paramIndex;
	}
	
	public void setParamIndex(int index)
	{
		this.paramIndex = index;
	}
	
	public String getAllocatedMethod()
	{
		return allocatedMethod;
	}
	
	public void setAllocatedMethod(String method)
	{
		this.allocatedMethod = method;
	}
	
	public boolean isMMRelease()
	{
		return isMMRelease;
	}
	
	public void setMMRelease(boolean isRelease)
	{
		this.isMMRelease = isRelease;
	}
	
	public boolean isMMAllocate()
	{
		return isMMAllocate;
	}
	
	public void setMMAllocate(boolean isAllocate)
	{
		this.isMMAllocate = isAllocate;
	}
	
	
	public final static String path = ".//gcc_lib//mm_method.property";
	public static Properties match = new Properties();
	
	static
	{
		try
		{
			InputStream in = new FileInputStream(path);
			match.load(in);
		}
		catch(Exception ex)
		{
			
		}
	}

}
