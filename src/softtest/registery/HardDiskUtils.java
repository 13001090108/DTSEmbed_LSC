package softtest.registery;

public class HardDiskUtils
{
	public static native String showHDSerial();

	static
	{
		// String lib =
		// System.getProperty("java.library.path").concat(File.pathSeparator).concat("out\\softtest\\registery\\java");
		// System.getProperties().put("java.library.path", lib);
		// System.out.println(System.getProperty("java.library.path"));
		System.loadLibrary("Sys");
	}

	public static String getHardDiskSN()
	{
		// System.out.println(showHDSerial());
		String hardSN = showHDSerial();
		if (null == hardSN)
		{
			return "";
		}
		return hardSN.trim();
	}

	public static String getSysInfo()
	{
		String info = "AFWG9DKDY5W7";
		String hardDiskSN = getHardDiskSN();

		if (hardDiskSN != null && !"".equalsIgnoreCase(hardDiskSN))
		{
			if (hardDiskSN.length() >= info.length())
			{
				info = hardDiskSN.substring(0, 12);
			}
			else
			{
				info = hardDiskSN + info.substring(hardDiskSN.length());
			}
		}

		return info;
	}

	/*
	 * public static String getHardDiskSN() { return "12345678"; }
	 * 
	 * public static void main(String[] args) { String hardSN =
	 * HardDiskUtils.getHardDiskSN(); System.out.println(hardSN); }
	 */
}