package softtest.registery;

import java.net.InetAddress;
import java.io.InputStream;
import java.io.BufferedInputStream;
import java.io.IOException;
import java.util.StringTokenizer;

public class NetworkUtils
{
	
	private static int MACADDR_LENGTH = 17;
	
	private static String WIN_OSNAME = "Windows";
	
	private static String WIN_MACADDR_REG_EXP = "^[0-9A-F]{2}-[0-9A-F]{2}-[0-9A-F]{2}-[0-9A-F]{2}-[0-9A-F]{2}-[0-9A-F]{2}$";
	
	private static String WIN_MACADDR_EXEC = "ipconfig /all";
	
	
	
	public static String getMacAddress()
	{
		String os = System.getProperty("os.name");
		// try
		// {
		if (os.startsWith(WIN_OSNAME))
		{
			return winMacAddress(winIpConfigCommand());
		} else
		{
			// throw new IOException("OS not supported : " + os);
			return "";
		}
		// }
		// catch(ParseException e)
		// {
		// e.printStackTrace();
		// throw new IOException(e.getMessage());
		// }
	}
	
	
	private static String winMacAddress(String ipConfigOutput) // throws
																// ParseException
	{
		// System.out.println("ipConfigOutput:"+ipConfigOutput);
		String localHost = null;
		try
		{
			localHost = InetAddress.getLocalHost().getHostAddress();
		}
		catch (java.net.UnknownHostException ex)
		{
			ex.printStackTrace();
			// throw new ParseException(ex.getMessage(), 0);
		}
		
		StringTokenizer tokenizer = new StringTokenizer(ipConfigOutput, "\n");
		String lastMacAddress = null;
		
		while (tokenizer.hasMoreTokens())
		{
			String line = tokenizer.nextToken().trim();
			
			
			// see if line contains IP address
			if (/* line.endsWith(localHost)&& */lastMacAddress != null)
			{
				return lastMacAddress;
			}
			
			
			// see if line contains MAC address
			int macAddressPosition = line.indexOf(":");
			if (macAddressPosition <= 0)
				continue;
			
			String macAddressCandidate = line.substring(macAddressPosition + 1)
					.trim();
			
			if (winIsMacAddress(macAddressCandidate))
			{
				lastMacAddress = macAddressCandidate;
				continue;
			}
		}
		
		return "";
		// ParseException ex = new ParseException
		// ("cannot read MAC address from [" + ipConfigOutput + "]", 0);
		// ex.printStackTrace();
		// throw ex;
	}
	
	
	private static boolean winIsMacAddress(String macAddressCandidate)
	{
		if (macAddressCandidate.length() != MACADDR_LENGTH)
			return false;
		if (!macAddressCandidate.matches(WIN_MACADDR_REG_EXP))
			return false;
		return true;
	}
	
	
	@SuppressWarnings("finally")
	private static String winIpConfigCommand()
	{
		String outputText = null;
		try
		{
			Process p = Runtime.getRuntime().exec(WIN_MACADDR_EXEC);
			InputStream stdoutStream = new BufferedInputStream(p
					.getInputStream());
			
			StringBuffer buffer = new StringBuffer();
			for (;;)
			{
				int c = stdoutStream.read();
				if (c == -1)
					break;
				buffer.append((char) c);
			}
			outputText = buffer.toString();
			stdoutStream.close();
		}
		catch (IOException e)
		{
			throw new RuntimeException("cannot get mac code", e);
		}
		finally
		{
			return outputText;
		}
		
	}
	
	
	// public static void main(String[] args)
	// {
	// try
	// {
	// System.out.println("MAC ADDRESS");
	// System.out.println(" OS : "
	// + System.getProperty("os.name"));
	// System.out.println(" IP/Localhost: "
	// + InetAddress.getLocalHost().getHostAddress());
	// System.out.println(" MAC Address : "
	// + getMacAddress());
	// }
	// catch(Throwable t)
	// {
	// t.printStackTrace();
	// }
	// }
}
