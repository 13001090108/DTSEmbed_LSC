package softtest.registery;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JOptionPane;

public class Initrialization implements ActionListener
{
	private InitrialFrame iFrame = null;
//	private SentinelUtils2 sentinel = null;
	private SmartNetUtil smartnet = null;
	
	private final static int basicClientCell = 0x04;
	private final static int basicLicenseCell = 0x00;
	
	/*
	private final static int maxCell = 54;
	*/
	//public final static int maxCell = 216;
	
	private int maxClientNum;
	
	public void startWork()
	{
		iFrame = new InitrialFrame();
		iFrame.setActionListener(this);
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
		if("NUM".equalsIgnoreCase(command))
		{
			enterNumAction();
		}
		if("LICENSE".equalsIgnoreCase(command))
		{
			enterLicenseAction();
		}
		
	}
	
	public void enterSizeAction()
	{
		String SizeStr = iFrame.getSizeChoice();
		
		maxClientNum = Integer.parseInt(SizeStr);
		
		iFrame.stateAfterSizeInput();
	}
	
	private void enterIPAction()
	{
		String ip = iFrame.getIPField();
		if(checkIP(ip))
		{
			try
			{
//				sentinel = SentinelUtils2.findSentinel(ip);
				if(smartnet == null) {
					smartnet = new SmartNetUtil();
				}
				smartnet.connect(ip);
				
				//以下内容用于测试  - 实际发布时需要删除
				/*for(int i=1; i<=54; i++)
				{
					sentinel.writeData(0, basicClientCell+i);
				}*/
				//end
				
				iFrame.createNumChoice(maxClientNum);
				
				iFrame.stateAfterIPInput();
			}
			catch (Exception ex)
			{
				JOptionPane.showMessageDialog(iFrame, ex.getMessage(), "ERROR!", JOptionPane.ERROR_MESSAGE);
				if(smartnet != null)
				{
					try
					{
						smartnet.disConnect();
					}
					catch (Exception e){}
				}
				iFrame.stateInitrial();
			}
		}
		else
		{
			iFrame.setWarningMessage("IP地址格式错误");
		}
		
	}
	   
	private void enterNumAction()
	{
		String numStr = iFrame.getNumChoice();
		try
		{
			int num = Integer.parseInt(numStr);				//这里的num能够保证小于maxClientNum
//			sentinel.overwriteData(num, basicClientCell, 1);
			smartnet.writeData(num, basicClientCell);
			
			if(maxClientNum == 54)
			{
				for(int i = 1; i <= num; i++)
				{
//					sentinel.writeData(0, basicClientCell + i + 1);
					smartnet.writeData(0, basicClientCell + i*4 + 1);
				}
			}
			
			if(maxClientNum == 216)
			{
				int addr;
				for(int i = 0; i < num; i++)
				{
					if(i%4 == 0)
					{
						addr = i/4 + 1;
//						sentinel.writeData(0, basicClientCell + addr);
						smartnet.writeData(0, basicClientCell + addr);
					}
				}
			}
			
			iFrame.stateAfterNumInput();
		}
		catch(NullPointerException ex)
		{
			iFrame.setWarningMessage("输入格式错误，请输入数字");
		}
		catch(NumberFormatException ex)
		{
			iFrame.setWarningMessage("输入格式错误，请输入数字");
		}
		catch(Exception ex)
		{
			JOptionPane.showMessageDialog(iFrame, ex.getMessage(), "ERROR!", JOptionPane.ERROR_MESSAGE);
			if(smartnet != null)
			{
				try
				{
//					sentinel.close();
					smartnet.disConnect();
				}
				catch (Exception e){}
			}
			iFrame.stateInitrial();
		}
	}
	
	private void enterLicenseAction()
	{
		String licenStr = iFrame.getLicenseField();
		boolean flag = true;
		try
		{
			int license = Integer.parseInt(licenStr);
//			sentinel.overwriteData(license, basicLicenseCell, 2);
			smartnet.writeData(license, basicLicenseCell);
			JOptionPane.showMessageDialog(iFrame, "设置成功：授权用户数量---" + iFrame.getNumChoice() + "; 重置许可次数---" + iFrame.getLicenseField(), 
					"SUCCESS!", JOptionPane.DEFAULT_OPTION);
		}
		catch(NullPointerException ex)
		{
			iFrame.setWarningMessage("输入格式错误，请输入数字");
			flag = false;
		}
		catch(NumberFormatException ex)
		{
			iFrame.setWarningMessage("输入格式错误，请输入数字");
			flag = false;
		}
		catch(Exception ex)
		{
			JOptionPane.showMessageDialog(iFrame, ex.getMessage(), "ERROR!", JOptionPane.ERROR_MESSAGE);
		}
		if(flag)
		{
			if(smartnet != null)
			{
				try
				{
//					sentinel.close();
					smartnet.disConnect();
				}
				catch (Exception e){}
			}
			iFrame.stateInitrial();
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
