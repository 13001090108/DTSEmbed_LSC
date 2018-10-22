package softtest.registery;

import java.security.MessageDigest;
import java.util.Random;

public class IdentityReg54 implements IdentityCheck
{
	public int checkIdentity(Identity id, SuperNet supernet, int base) throws Exception
	{
		int data = supernet.readData(base + id.getCellAddress() * 4 + 1);
			
		if(data != 0)
		{
			return 4;

		}
		
		byte[] extraMessage = new byte[2];
//		byte[] extraMessage = new byte[1];
		Random random = new Random();
		do
		{
			random.nextBytes(extraMessage);
		}
		while(extraMessage[0]== 0 && extraMessage[1] == 0);
//		 while(extraMessage[0] == 0);
				
		String hardDiskSN = HardDiskUtils.getHardDiskSN();
		String str = hardDiskSN.concat(new String(extraMessage));
		MessageDigest digest = MessageDigest.getInstance("SHA-1");
		byte[] outcome = digest.digest(str.getBytes());
		String signature = new String(outcome);
		
		id.setSignature(signature);
				
		data = ((int)extraMessage[1]) & 0xFF;
		data = data << 8;
		data = data ^ (((int)extraMessage[0]) & 0xFF);
		
//		data = ((int)extraMessage[0]) & 0xFF;
		supernet.writeData(data, id.getCellAddress()*4 + 1 + base);

		return 0;
	}
}
