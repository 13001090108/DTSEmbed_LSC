package softtest.registery.file;

import javax.swing.JOptionPane;

public class RegTest
{
	public static void main(String[] args)
	{
		/*int result = Register.verify();

		if (result == Register.UNREGISTERED)
		{
			RegViewer.launch();
			return;
		}

		if (result == Register.ERROR)
		{
			JOptionPane.showMessageDialog(null, "用户操作不当引起错误", "ERROR!",
					JOptionPane.ERROR_MESSAGE);
			return;
		}*/
		int result = Register.verify();

		if (result == Register.UNREGISTERED)
		{
			RegViewer.launch();
			return;
		}

		if (result == Register.ERROR)
		{
			// JOptionPane.showMessageDialog(null, "用户操作不当引起错误", "ERROR!",
			// JOptionPane.ERROR_MESSAGE);
			Reset.launch();
			return;
		}

		System.out.println("start DTS");
	}
}
