
package softtest.registery;

import javax.swing.JOptionPane;

import softtest.config.c.Config;
import LONGMAI.NoxTimerKey;

public class SysInfo {
	public static boolean checkPermission() {
		NoxTimerKey aNox = new NoxTimerKey();
		int [] keyHandles =  new int[8];
		int [] nKeyNum = new int[1];
		int nAppID = 0xFFFFFFFF;
		//查找加密锁
        if( 0 != aNox.NoxFind(nAppID, keyHandles, nKeyNum))
        {
        	JOptionPane.showMessageDialog(null, "请插入加密锁！");
            return false;
        }
        //System.out.println("找到"+nKeyNum[0]+"只锁");
        //System.out.println(UID);
       //打开第一个加密锁3e50fbc633fbfe24
        if( 0 != aNox.NoxOpen(keyHandles[0], "3e50fbc633fbfe24"))
        {
        	 JOptionPane.showMessageDialog(null, "加密锁错误或者已经过期！");
             System.out.println(aNox.NoxGetLastError());
             return false;
        }
        aNox.NoxClose(keyHandles[0]);
        //System.out.println("加密锁已关闭");
        return true;
	}
	public static int getPhase() {
		NoxTimerKey aNox = new NoxTimerKey();
		int [] keyHandles =  new int[8];
		int [] nKeyNum = new int[1];
		int nAppID = 0xFFFFFFFF;
		int nRtn = 0;
		//获得次数限制信息
        int [] nRemain = new int[1];
        int [] nMax = new int[1];
        int [] Mode2 = new int[1];
        
      //查找加密锁        if( 0 != aNox.NoxFind(nAppID, keyHandles, nKeyNum))
        if( 0 != aNox.NoxFind(nAppID, keyHandles, nKeyNum))
        {
        	    JOptionPane.showMessageDialog(null, "找不到加密锁！");
                return -1;
        }
        //System.out.println("找到"+nKeyNum[0]+"只锁");
        nRtn =aNox.NoxGetRemnantCount(keyHandles[0],nRemain,nMax,Mode2);
        if(nRtn != 0)
        {
                System.out.println("获得次数限制信息失败");
                System.out.println(aNox.NoxGetLastError());
                return -1;
        }
    	int all =nMax[0];
		int left =nRemain[0];	
		int num = all/Config.PHASE_NUMUBER;
	    int total=(all-left) /num +1;
	    if(total>Config.PHASE_NUMUBER){
	    	 JOptionPane.showMessageDialog(null, "加密锁已过期！");
             System.exit(0);
	    }
		return total;  
	}
	
	public static String getHardSN() {
		if (Config.PHASE_REGISTER) {
			int phase = getPhase();
			return getHardDiskSN() + phase;
		}
        return getHardDiskSN();
	}
	
	public static String getHardDiskSN() {
		String ret = "AFWG9DKDY5W7";
		String hardDiskSN=HardDiskUtils.getHardDiskSN().trim();   //获取硬盘序列号
		if(null!=hardDiskSN&&!hardDiskSN.equals(""))
		{
			if (hardDiskSN.length() >= ret.length()) {
				ret = hardDiskSN.substring(0,12);
			} else {
				ret = hardDiskSN + ret.substring(hardDiskSN.length());
			}
		}
		return ret;
	}
}
