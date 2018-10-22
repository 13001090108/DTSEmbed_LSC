package softtest.registery;


import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JTextField;

import softtest.config.c.Config;
import softtest.config.c.SuccessRe;


public class RegisteryClient extends JFrame {

	private static final long serialVersionUID = 1L;
	final JLabel promptLabel = new JLabel();
	final JLabel hardWareSNLabel = new JLabel();
	final JLabel softWareSNLabel = new JLabel();
	final JTextField hardWareSNTextField = new JTextField();
	final JTextField softWareSNTextField = new JTextField();
	final JButton regButton = new JButton();
	String hardWareSNSysStr="";
	private static RegisteryClient current = null;
	
	public void launchFrame()
	{
		current = this;
		hardWareSNSysStr = SysInfo.getHardSN();

		getContentPane().setLayout(null);
		if (Config.PHASE_REGISTER) {			
		   this.setTitle("Èí¼þ×¢²á(" + SysInfo.getPhase() + "/" + Config.PHASE_NUMUBER + ")");
		} else {
			 this.setTitle("Èí¼þ×¢²á");
		}
		setBounds(100, 100, 423, 196);
		setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);

		promptLabel.setText("Çë·ÃÎÊÒÔÏÂÕ¾µã»ñÈ¡×¢²áÂë£ºhttp://www.dtstesting.com");
		promptLabel.setBounds(10, 13, 366, 18);
		getContentPane().add(promptLabel);

		hardWareSNLabel.setText("ÐòÁÐºÅ£º");
		hardWareSNLabel.setBounds(10, 43, 66, 18);
		getContentPane().add(hardWareSNLabel);

		
		softWareSNLabel.setText("×¢²áÂë£º");
		softWareSNLabel.setBounds(10, 72, 66, 18);
		getContentPane().add(softWareSNLabel);

		
		hardWareSNTextField.setText(hardWareSNSysStr);
		hardWareSNTextField.setBounds(94, 41, 302, 22);
		hardWareSNTextField.setEditable(false);
		getContentPane().add(hardWareSNTextField);
        
		
		softWareSNTextField.setText("");
		softWareSNTextField.setBounds(94, 70, 302, 22);
		getContentPane().add(softWareSNTextField);

		regButton.addActionListener(new ActionListener() {
			public void actionPerformed(final ActionEvent event) {
				String hardWareSNStr=hardWareSNTextField.getText();

				String softWareSNStr=softWareSNTextField.getText();
				String softWareSNSysStr=Encrypt.encryptHardInfo(hardWareSNSysStr);
				boolean rightRe=(null!=softWareSNSysStr&&null!=softWareSNStr&&softWareSNStr.equals(softWareSNSysStr));
				SuccessRe.setR(rightRe);
				if(rightRe)
				{
//					System.out.println("×¢²á³É¹¦!");
					Registery.writeValue(Config.version, hardWareSNStr, softWareSNStr);
					JOptionPane.showMessageDialog(null,"×¢²á³É¹¦,¸ÐÐ»ÄúµÄÊ¹ÓÃ£¡");
					RegisteryClient.current.dispose();
				} 
				else
				{
//					System.out.println("×¢²áÊ§°Ü£¬Çë¹ºÂòÕý°æ!");
					JOptionPane.showMessageDialog(null,"×¢²áÊ§°Ü£¬Çë¹ºÂòÕý°æ£¡","Èí¼þ×¢²á",JOptionPane.ERROR_MESSAGE); 
				}
				
			}
		});
		regButton.setText("×¢²á");
		regButton.setBounds(129, 107, 106, 28);
		getContentPane().add(regButton);

	}
	/**
	 * @param args
	 */
	public static void main(String[] args) {
		if (Config.PHASE_REGISTER) {
			if (SysInfo.getPhase() < 0) {
				JOptionPane.showMessageDialog(null, "Çë²åÈë¼ÓÃÜËø£¡");
				return;
			}
		}
		RegisteryClient client = new RegisteryClient();
		client.launchFrame();
		client.setVisible(true);
	}

}
