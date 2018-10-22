package softtest.registery;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JOptionPane;

public class Reset implements ActionListener
{
	private ResetFrame rFrame = null;
//	private SentinelUtils2 sentinel = null;
	private SmartNetUtil smartnet = null;

	private int numLicense = 0;
	
	private int maxClientNum;
	
	private final static int basicClientCell = 0x04;
	private final static int basicLicenseCell = 0x00;
	
	public void startWork()
	{
		rFrame = new ResetFrame();
		rFrame.setActionListener(this);
	}
	
	public void actionPerformed(ActionEvent event)
	{
		String command = event.getActionCommand().toUpperCase();
		if("SIZE".equalsIgnoreCase(command))
		{
			enterSizeAction();
		}
		if("IP".equalsIgnoreCase(command))
		{
			enterIPAction();
		}
		if("ADDR".equalsIgnoreCase(command))
		{
			enterAddrAction();
		}
		
	}
	
	public void enterSizeAction()
	{
		String SizeStr = rFrame.getSizeChoice();
		
		maxClientNum = Integer.parseInt(SizeStr);
		
		rFrame.stateAfterSizeInput();
	}
	
	private void enterIPAction()
	{
		String ip = rFrame.getIPField();
		if(checkIP(ip))
		{
			boolean release = false;
			try
			{
//				sentinel = SentinelUtils2.findSentinel(ip);
				if(smartnet == null) {
					smartnet = new SmartNetUtil();
				}
				smartnet.connect(ip);
				getNumLicense();
				if(numLicense > 0)
				{
					createAddressChoice();
					rFrame.stateAfterIPInput();
				}
				else
				{
					release = true;
					JOptionPane.showMessageDialog(rFrame, "重置许可次数为零，操作不能够进行", "ERROR!", JOptionPane.ERROR_MESSAGE);
				}
			}
			catch(Exception ex)
			{
				release = true;
				rFrame.stateInitial();
				JOptionPane.showMessageDialog(rFrame, ex.getMessage(), "ERROR!", JOptionPane.ERROR_MESSAGE);
			}
//			if(release && sentinel != null)
			if(release && smartnet != null)
			{
				try
				{
					smartnet.disConnect();
				}
				catch (Exception e){}
			}
		}
		else
		{
			rFrame.setWarningMessage("IP地址格式错误");
		}
		
	}
	   
	private void enterAddrAction()
	{
		try
		{
			String cellStr = rFrame.getAddrChoice();
			int cellAddr = Integer.parseInt(cellStr);
			
			smartnet.decrement(basicLicenseCell);
//			if(flag == false) {
//				JOptionPane.showMessageDialog(rFrame, "重置次数已经用完，请联系管理员进行解决！！！");
//			}
			
			if(maxClientNum == 54)
			{
				smartnet.writeData(0, cellAddr*4 + 1 + basicClientCell);
			}
			if(maxClientNum == 216)
			{
				int cell = (cellAddr - 1)/4 + 1;
				int offset = (cellAddr - 1)%4*4;
				int data = smartnet.readData(basicClientCell + cell);
				int tmp = 0xFFFFFFFF ^ (0xF << offset);
				data = data & tmp;
				smartnet.writeData(data, cell+ basicClientCell);
			}
			
			
			numLicense--;
			JOptionPane.showMessageDialog(rFrame, "重置成功，剩余许可次数为：" + numLicense , "SUCCESS!", JOptionPane.DEFAULT_OPTION);
		}
		catch(NullPointerException ex)
		{
			JOptionPane.showMessageDialog(rFrame, "尚未有用户注册", "WARNING!", JOptionPane.WARNING_MESSAGE);
		}
		catch(Exception ex)
		{
			JOptionPane.showMessageDialog(rFrame, ex.getMessage(), "ERROR!", JOptionPane.ERROR_MESSAGE);
		}
		
		rFrame.stateInitial();
		if(smartnet != null)
		{
			try
			{
				smartnet.disConnect();
			}
			catch (Exception e){}
		}
	}
	
	private void getNumLicense() throws Exception
	{
		numLicense = smartnet.readData(basicLicenseCell);
		rFrame.setWarningMessage("剩余重置许可次数为：" + numLicense);
	}
	
	private void createAddressChoice() throws Exception
	{	
		int numClient = smartnet.readData(basicClientCell);
		int data = 0;
		
		if(numClient > maxClientNum)
		{
			throw new Exception("容量错误");
		}
		
		if(maxClientNum == 54)
		{
			for(int i=1; i<=numClient; i++)
			{
				data = smartnet.readData(i*4 + 1 + basicClientCell);
				if(data != 0)
				{
					rFrame.addAddressItem(i);
				}
			}
		}
		
		if(maxClientNum == 216)
		{
			int addr;
			int offset;
			for(int i=0; i<numClient; i++)
			{
				addr = i/4 + 1;
				offset = (i%4)*4;
				data = smartnet.readData(addr + basicClientCell);
				data = data >> offset;
				data = data & 0xF;
				if(data != 0)
				{
					rFrame.addAddressItem(i + 1);
				}
			}
		}
	}
	
	private boolean checkIP(String ip)
	{
		boolean result;
		try
		{
			String regex = "(0|([1-9]\\d?)|(1\\d{2})|(2[0-4]\\d)|(25[0-5]))" + "\\."
						+ "(0|([1-9]\\d?)|(1\\d{2})|(2[0-4]\\d)|(25[0-5]))" + "\\."
						+ "(0|([1-9]\\d?)|(1\\d{2})|(2[0-4]\\d)|(25[0-5]))" + "\\."
						+ "(0|([1-9]\\d?)|(1\\d{2})|(2[0-4]\\d)|(25[0-5]))";
			result = ip.matches(regex);
		}
		catch(Exception ex)
		{
			result = false;
		}
		return result;
	}
}
