package softtest.registery;

import org.longmai.SmartNet.SmartNetLib;

public class SuperNet {
	private SmartNetLib smartnet = null;
	private static int port = 8088;
	private static int heartbeat = 70;
	
	public SuperNet() {
		smartnet = SmartNetLib.getInstance();
	}

	private int validation() {
		int rtn = smartnet.SmartNetOpen(1639095144, -1355634854, -1485101938, 1049275498);
		if(rtn != 0){
			System.out.println("验证网络锁密码失败,错误码："+smartnet.SmartNetGetLastError());
		}else{
			System.out.println("验证网络锁密码成功");
		}
		return rtn;
	}
	
	public SmartNetLib getSmartnet() {
		return smartnet;
	}
	
	public int connect(String ip) {
		//smartnet = SmartNetLib.getInstance();
		int rtn = smartnet.SmartNetConnect(ip, port, heartbeat);
		if(rtn != 0){
			System.out.println("未连接成功,错误码："+smartnet.SmartNetGetLastError());
		}else{
			System.out.println("连接成功");
		}
		return rtn;
	}
	
	public int readData(int cell) {
		validation();
		byte [] pBuffer = new byte[4];
		for(int i=0; i<pBuffer.length; i++) {
			pBuffer[i] = 0;
		}
		int rtn=smartnet.SmartNetReadStorage(cell, 4, pBuffer);
		if(rtn!=0){
	    	System.out.println("读取存储区失败,错误码为："+smartnet.SmartNetGetLastError());
	    }else{
	    	System.out.println("读取存储区成功"); 
	    }
		int ans = 0;
		ans = ((int)pBuffer[3]) & 0xFF;
		ans <<= 8;
		ans = ans ^ (((int)pBuffer[2]) & 0xFF);
		ans <<= 8;
		ans = ans ^ (((int)pBuffer[1]) & 0xFF);
		ans <<= 8;
		ans = ans ^ (((int)pBuffer[0]) & 0xFF);
		
		return ans;
	}

	public void writeData(int data, int cell) {
		validation();
		byte[] pBuffer = new byte[4];
		pBuffer[0] = (byte)data;
		pBuffer[1] = (byte)((data>>8) & 0xFF);
		pBuffer[2] = (byte)((data>>16) & 0xFF);
		pBuffer[3] = (byte)((data>>24) & 0xFf);
	    int rtn=smartnet.SmartNetWriteStorage(cell, 4, pBuffer);
	    if(rtn!=0){
	    	System.out.println("写存储区失败,错误码为："+smartnet.SmartNetGetLastError());
	    }else if(rtn==0){
	    	System.out.println("写存储区成功");
	    } 
	}
	
	public int disConnect() {
		int rtn = smartnet.SmartNetDisConnect();
		return rtn;
	}
}
