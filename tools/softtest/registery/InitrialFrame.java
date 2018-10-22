package softtest.registery;


import java.awt.Choice;
import java.awt.Component;
import java.awt.Container;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.ButtonGroup;
import javax.swing.GroupLayout;
import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JRadioButton;
import javax.swing.JTextField;
import javax.swing.SwingConstants;
import javax.swing.SwingUtilities;
import javax.swing.UIManager;
import javax.swing.UnsupportedLookAndFeelException;

public class InitrialFrame extends JFrame
{
	private JLabel serverIPLabel;
	private JTextField serverIPTextField;
	private JButton enterIPButton;
	
	private JLabel clientLicenseLabel;
	private JTextField clientLicenseTextField;
	private JButton enterLicenseButton;
	
	private JLabel clientNumLabel;
	private Choice clientNumChoice;
	private JButton enterNumButton;
	
	private JLabel lockSizeLabel;
	private Choice lockSizeChoice;
	private JButton enterSizeButton;
	
	
	private JLabel warningMessageLabel;
	
	public InitrialFrame()
	{	
		lockSizeLabel = new JLabel("选择锁的容量：");
		lockSizeChoice = new Choice();
		enterSizeButton = new JButton("选择锁的容量");
		enterSizeButton.setActionCommand("SIZE");
		lockSizeChoice.setEnabled(true);
		enterSizeButton.setEnabled(true);
		createSizeChoice();
		
		serverIPLabel = new JLabel("IP地址：");
		serverIPTextField = new JTextField();
		enterIPButton = new JButton("输入IP地址");
		enterIPButton.setActionCommand("IP");
		enterIPButton.setEnabled(false);
		//serverIPTextField.setFocusable(true);
		serverIPTextField.setEnabled(false);
		
		clientLicenseLabel = new JLabel("重置许可次数：");
		clientLicenseTextField = new JTextField("");
		enterLicenseButton = new JButton("输入许可次数");
		enterLicenseButton.setActionCommand("LICENSE");
		clientLicenseTextField.setEnabled(false);
		enterLicenseButton.setEnabled(false);
		
		clientNumLabel = new JLabel("授权用户数量：");
		clientNumChoice = new Choice();
		enterNumButton = new JButton("输入用户数量");
		enterNumButton.setActionCommand("NUM");
		clientNumChoice.setEnabled(false);
		enterNumButton.setEnabled(false);
		//createNumChoice();                         //???
		
		warningMessageLabel = new JLabel("");
		
		Container c = this.getContentPane();
	    GroupLayout layout = new GroupLayout(c);
	    c.setLayout(layout);

	    layout.setAutoCreateGaps(true);
	    layout.setAutoCreateContainerGaps(true);
	    
	    GroupLayout.ParallelGroup h1a = layout.createParallelGroup(GroupLayout.Alignment.LEADING);
	    h1a.addComponent(lockSizeLabel);
	    h1a.addComponent(serverIPLabel);
	    h1a.addComponent(clientNumLabel);
	    h1a.addComponent(clientLicenseLabel);
	    
	    GroupLayout.ParallelGroup h1b = layout.createParallelGroup(GroupLayout.Alignment.LEADING);
	    h1b.addComponent(lockSizeChoice);
	    h1b.addComponent(serverIPTextField);
	    h1b.addComponent(clientNumChoice);
	    h1b.addComponent(clientLicenseTextField);
	    
	    GroupLayout.ParallelGroup h1c = layout.createParallelGroup(GroupLayout.Alignment.LEADING);
	    h1c.addComponent(enterSizeButton);
	    h1c.addComponent(enterIPButton);
	    h1c.addComponent(enterLicenseButton);
	    h1c.addComponent(enterNumButton);
	    
	    GroupLayout.SequentialGroup h1 = layout.createSequentialGroup();
	    h1.addGroup(h1a);
	    h1.addGroup(h1b);
	    h1.addGroup(h1c);
	    
	    GroupLayout.ParallelGroup h2 = layout.createParallelGroup(GroupLayout.Alignment.CENTER);
	    h2.addGroup(h1);
	    h2.addComponent(warningMessageLabel);
	    
	    layout.setHorizontalGroup(h2);
	    
	    layout.linkSize(SwingConstants.HORIZONTAL, new Component[] { enterSizeButton, enterIPButton, enterLicenseButton, enterNumButton });
	    
	    GroupLayout.ParallelGroup v0 = layout.createParallelGroup(GroupLayout.Alignment.CENTER);
	    v0.addComponent(lockSizeLabel);
	    v0.addComponent(lockSizeChoice);
	    v0.addComponent(enterSizeButton);
	    
	    GroupLayout.ParallelGroup v1 = layout.createParallelGroup(GroupLayout.Alignment.CENTER);
	    v1.addComponent(serverIPLabel);
	    v1.addComponent(serverIPTextField);
	    v1.addComponent(enterIPButton);
	    
	    GroupLayout.ParallelGroup v3 = layout.createParallelGroup(GroupLayout.Alignment.CENTER);
	    v3.addComponent(clientLicenseLabel);
	    v3.addComponent(clientLicenseTextField);
	    v3.addComponent(enterLicenseButton);
	    
	    GroupLayout.ParallelGroup v2 = layout.createParallelGroup(GroupLayout.Alignment.CENTER);
	    v2.addComponent(clientNumLabel);
	    v2.addComponent(clientNumChoice);
	    v2.addComponent(enterNumButton);
	    
	    layout.setVerticalGroup(layout.createSequentialGroup().addGroup(v0).addGroup(v1).addGroup(v2).addGroup(v3).addComponent(warningMessageLabel));
	    
	    layout.linkSize(SwingConstants.VERTICAL,new Component[] { lockSizeChoice, serverIPTextField, clientLicenseTextField, clientNumChoice });
		
	    try
		{
			UIManager.setLookAndFeel(UIManager.getSystemLookAndFeelClassName());
			SwingUtilities.updateComponentTreeUI(this); 	
		}
		catch (Exception ex){}
	    
		this.setTitle("网络锁初始化");
	    //this.setBounds(400, 550, 400, 160);
		this.setBounds(400, 550, 480, 190);
		this.setDefaultCloseOperation(EXIT_ON_CLOSE);
		
		this.setVisible(true);

	}
	
	public String getSizeChoice()
	{
		return lockSizeChoice.getSelectedItem().trim();
	}
	
	public String getIPField()
	{
		return serverIPTextField.getText().trim(); 
	}
	
	public String getNumChoice()
	{
		return clientNumChoice.getSelectedItem().trim();
	}
	
	public String getLicenseField()
	{
		return clientLicenseTextField.getText().trim();
	}
	
	public void setWarningMessage(String message)
	{
		warningMessageLabel.setText(message);
	}
	
	private void createSizeChoice()
	{
		lockSizeChoice.add(Integer.toString(54));
		lockSizeChoice.add(Integer.toString(216));
	}
	
	public void createNumChoice(int size)
	{
		for(int i=0; i<size; i++)  
		{
			clientNumChoice.add(Integer.toString(i+1));
		}
	}
	
	public void setActionListener(ActionListener listener)
	{
		enterSizeButton.addActionListener(listener);
		enterIPButton.addActionListener(listener);
		enterNumButton.addActionListener(listener);
		enterLicenseButton.addActionListener(listener);
	}
	
	
	public void stateAfterSizeInput()
	{
		lockSizeChoice.setEnabled(false);
		enterSizeButton.setEnabled(false);
		
		serverIPTextField.setEnabled(true);
		enterIPButton.setEnabled(true);
		
		clientNumChoice.setEnabled(false);
		enterNumButton.setEnabled(false);
		
		clientLicenseTextField.setEnabled(false);
		enterLicenseButton.setEnabled(false);
		
		warningMessageLabel.setText("");
	}
	
	public void stateAfterIPInput()
	{
		lockSizeChoice.setEnabled(false);
		enterSizeButton.setEnabled(false);
		
		serverIPTextField.setEnabled(false);
		enterIPButton.setEnabled(false);
		
		clientNumChoice.setEnabled(true);
		enterNumButton.setEnabled(true);
		
		clientLicenseTextField.setEnabled(false);
		enterLicenseButton.setEnabled(false);
		
		warningMessageLabel.setText("");
	}
	
	public void stateInitrial()  
	{
		lockSizeChoice.setEnabled(true);
		enterSizeButton.setEnabled(true);
		
		serverIPTextField.setEnabled(false);
		serverIPTextField.setText("");
		enterIPButton.setEnabled(false);
		
		clientNumChoice.setEnabled(false);
		clientNumChoice.removeAll();   //???
		enterNumButton.setEnabled(false);
		
		clientLicenseTextField.setEnabled(false);
		enterLicenseButton.setEnabled(false);
		clientLicenseTextField.setText("");
		
		warningMessageLabel.setText("");
	}
	
	
	public void stateAfterNumInput()
	{
		lockSizeChoice.setEnabled(false);
		enterSizeButton.setEnabled(false);
		
		serverIPTextField.setEnabled(false);
		enterIPButton.setEnabled(false);
		
		clientNumChoice.setEnabled(false);
		enterNumButton.setEnabled(false);
		
		clientLicenseTextField.setEnabled(true);
		enterLicenseButton.setEnabled(true);
		
		warningMessageLabel.setText("");
	}
	
	
	public static void main(String[] args)
	{
		InitrialFrame aFrame = new InitrialFrame();
	}

}
