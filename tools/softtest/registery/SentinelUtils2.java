package softtest.registery;

public class SentinelUtils2
{	
	private byte[] apiPacket = new byte[SentinelSuperpro.API_PACKET_SZ];
	private int developerID = 0x3B88;
	private int writePassword = 0x5F6E;
	private int overwritePassword1 = 0xE0B0;
	private int overwritePassword2 = 0x35C4;
	
	private static SentinelUtils2 senUtils = null;
	public static SentinelUtils2 findSentinel(String ip) throws Exception
	{
		if(senUtils != null)
		{
			senUtils.close();
			senUtils = null;
		}
		
		senUtils = new SentinelUtils2(ip);
		
		return senUtils;
	}
	
	private SentinelUtils2(String ip) throws Exception
	{
		connect(ip);
	}
	
	private void connect(String ip) throws Exception
	{
		SentinelSuperpro.RNBOsproFormatPacket(apiPacket, apiPacket.length);
		SentinelSuperpro.RNBOsproInitialize(apiPacket);
		SentinelSuperpro.RNBOsproSetContactServer(apiPacket, ip);
		int spStatus = SentinelSuperpro.RNBOsproFindFirstUnit(apiPacket, developerID);
		if(spStatus != 0)
		{
			throw new Exception("some error_" + spStatus + " has happened when connect to " + ip);
		}
		//SentinelSuperpro.RNBOsproSetHeartBeat(apiPacket, SentinelSuperpro.INFINITE_HEARTBEAT);
		//SentinelSuperpro.RNBOsproSetHeartBeat(apiPacket, 1800);
		SentinelSuperpro.RNBOsproSetHeartBeat(apiPacket, 600);
	}
	
	public int readData(int cell) throws Exception
	{
		int[] data = new int[1];
		int spStatus = SentinelSuperpro.RNBOsproRead(apiPacket, cell, data);
		if(spStatus != 0)
		{
			throw new Exception("some error_" + spStatus + " has happened when read data from server");
		}
		return data[0];
	}
	
	public void writeData(int data, int cell) throws Exception
	{
		int spStatus = SentinelSuperpro.RNBOsproWrite(apiPacket, writePassword, cell, data, (byte)0);
		if(spStatus != 0)
		{
			throw new Exception("some error_" + spStatus + " has happened when write data to server");
		}
	}
	
	public void overwriteData(int data, int cell, int acessCode) throws Exception
	{
		int spStatus = SentinelSuperpro.RNBOsproOverwrite(apiPacket, writePassword, overwritePassword1, overwritePassword2, cell, data, (byte)acessCode);
		if(spStatus != 0)
		{
			throw new Exception("some error_" + spStatus + " has happened when write data to server");
		} 
	}
	
	public void decrement(int cell) throws Exception
	{
		int spStatus = SentinelSuperpro.RNBOsproDecrement(apiPacket, writePassword, cell);
		if(spStatus != 0)
		{
			throw new Exception("some error_" + spStatus + " has happened when do decrement");
		}
	}
	
	public void close() throws Exception
	{
		int spStatus = SentinelSuperpro.RNBOsproReleaseLicense(apiPacket, 0, new int[]{0});
		if(spStatus != 0)
		{
			throw new Exception("some error_" + spStatus + " has happened when release license");
		}
		SentinelSuperpro.RNBOsproCleanup();
	}
	
	
	
}
