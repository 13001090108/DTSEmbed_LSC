package softest.registery.file.resetAuth;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.IOException;

import javax.swing.JOptionPane;

import sun.misc.BASE64Decoder;

public class ResetAuth implements ActionListener
{
	private ResetAuthFrame rFrame;

	public ResetAuth()
	{
		rFrame = new ResetAuthFrame();
	}

	public void work()
	{
		rFrame.addActionLisener(this);
		rFrame.setVisible(true);
	}

	public void actionPerformed(ActionEvent event)
	{
		try
		{
			String req = rFrame.getReqField();
			String response = creatResponse(req);
			rFrame.setRespondField(response);
		}
		catch (IOException e)
		{
			e.printStackTrace();
			JOptionPane.showMessageDialog(rFrame, "       有异常发生，响应码生成失败！",
					"ERROR!", JOptionPane.ERROR_MESSAGE);
		}

	}

	private String creatResponse(String req) throws IOException
	{
		byte[] en = (new BASE64Decoder()).decodeBuffer(req);
		StringBuffer sb = new StringBuffer();
		for (int i = 0; i < en.length; i++)
		{

			sb.append(Integer.toHexString(en[i] & 0xFF));
		}

		return sb.toString().toUpperCase();
	}

	public static void main(String[] args)
	{
		new ResetAuth().work();
	}
}
