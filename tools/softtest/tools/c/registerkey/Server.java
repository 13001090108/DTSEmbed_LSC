package softtest.tools.c.registerkey;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JTextField;

import softtest.registery.Encrypt;

/**
 * 注册码生成器：根据软件所运行的硬件环境，生成注册码
 * @author huchengjie	
 * 2010-5-17
 */
public class Server extends JFrame {
	private static final long serialVersionUID = 1L;
	final JLabel hardWareSNLabel = new JLabel();
	final JLabel softWareSNLabel = new JLabel();
	final JTextField hardWareSNTextField = new JTextField();
	final JTextField softWareSNTextField = new JTextField();
	final JButton regButton = new JButton();
	
	
	public void launchFrame()
	{
		getContentPane().setLayout(null);
		this.setTitle("注册码生成器");
		setBounds(100, 100, 423, 196);
		setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);

		
		hardWareSNLabel.setText("硬件型号：");
		hardWareSNLabel.setBounds(10, 33, 66, 18);
		getContentPane().add(hardWareSNLabel);

		
		softWareSNLabel.setText("序列号：");
		softWareSNLabel.setBounds(10, 62, 66, 18);
		getContentPane().add(softWareSNLabel);

		
		hardWareSNTextField.setText("");
		hardWareSNTextField.setBounds(94, 31, 302, 22);
		getContentPane().add(hardWareSNTextField);
        
		
		softWareSNTextField.setText("");
		softWareSNTextField.setBounds(94, 60, 302, 22);
		softWareSNTextField.setEditable(false);
		getContentPane().add(softWareSNTextField);


		regButton.addActionListener(new ActionListener() {
			public void actionPerformed(final ActionEvent event) {
				String hardWareSNStr=hardWareSNTextField.getText();
				String softWareSNStr=Encrypt.encrypt(hardWareSNStr);
				if (hardWareSNStr.length() > 12) {
					String hardSN = hardWareSNStr.substring(0, 12);
					int phase = Integer.parseInt(hardWareSNStr.substring(12));
					softWareSNStr = Encrypt.encryptHardInfoPhase(hardSN, phase);
				}
				softWareSNTextField.setText(softWareSNStr);
				
			}
		});
		regButton.setText("生成注册码");
		regButton.setBounds(129, 107, 106, 28);
		getContentPane().add(regButton);

	}
	/**
	 * @param args
	 */
	public static void main(String[] args) {
//		System.out.println(Sys.getHardDiskSN());
//	    System.out.println(MyEncrypt.Encrypt(Sys.getHardDiskSN(),"MD5"));
//		
		Server server=new Server();
		server.launchFrame();
		server.setVisible(true);
	
	}

}
 