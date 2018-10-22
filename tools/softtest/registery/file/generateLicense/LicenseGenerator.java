package softtest.registery.file.generateLicense;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JOptionPane;
import javax.swing.UIManager;

import softtest.registery.file.RegIdentity;

public class LicenseGenerator implements ActionListener
{
	GenFrame gFrame;

	static
	{
		try
		{
			UIManager.setLookAndFeel(UIManager.getSystemLookAndFeelClassName());
		}
		catch (Exception ex)
		{
		}
	}

	public static void launch()
	{
		new LicenseGenerator();
	}

	private LicenseGenerator()
	{
		gFrame = new GenFrame();
		gFrame.addActionLisener(this);
		gFrame.setVisible(true);
	}

	public void actionPerformed(ActionEvent event)
	{
		gFrame.stateAfterInput();

		String sn = gFrame.getSNField();
		String n = gFrame.getNumField();

		RegIdentity license = generate(sn, n);

		if (license != null)
		{
			String key = license.getID();
			String fName = key + GenConstants.SUFFIX;
			GenUtils.saveToEncryptFile(key, license, GenConstants.OUTPUT_PATH,
					fName);

			JOptionPane.showMessageDialog(gFrame, "授权文件已生成，存放在路径"
					+ GenConstants.OUTPUT_PATH + "下！", "SUCCESS!",
					JOptionPane.PLAIN_MESSAGE);

			gFrame.stateInitial();
		}
		else
		{
			JOptionPane.showMessageDialog(gFrame, "输入错误，不能够生成授权文件！", "ERROR!",
					JOptionPane.ERROR_MESSAGE);
			gFrame.stateErrorInput();
		}
	}

	private RegIdentity generate(String sn, String n)
	{
		RegIdentity rID;

		try
		{
			String id = sn.substring(0, 12);
			int num = Integer.parseInt(n);
			String sseq = sn.substring(12);
			int seq = Integer.parseInt(sseq);

			rID = new RegIdentity(id, num, seq);
		}
		catch (Exception ex)
		{
			rID = null;
		}

		return rID;
	}

	public static void main(String[] args)
	{
		LicenseGenerator.launch();
	}

}
