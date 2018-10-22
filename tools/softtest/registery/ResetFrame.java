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

public class ResetFrame extends JFrame
{
	private JLabel serverIPLabel;
	private JTextField serverIPTextField;
	private JButton enterIPButton;
	
	private JLabel cellAddrLabel;
	private Choice cellAddrChoice;
	private JButton enterAddrButton;
	
	private JLabel lockSizeLabel;
	private Choice lockSizeChoice;
	private JButton enterSizeButton;
	
	private JLabel warningMessageLabel;
	
	public ResetFrame()
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
		//serverIPTextField.setFocusable(true);
		serverIPTextField.setEnabled(false);
		enterIPButton.setEnabled(false);
		
		cellAddrLabel = new JLabel("序列号：");
		cellAddrChoice = new Choice();
		enterAddrButton = new JButton("输入序列号");
		enterAddrButton.setActionCommand("ADDR");
		cellAddrChoice.setEnabled(false);
		enterAddrButton.setEnabled(false);
		
		warningMessageLabel = new JLabel("");
		
		Container c = this.getContentPane();
	    GroupLayout layout = new GroupLayout(c);
	    c.setLayout(layout);

	    layout.setAutoCreateGaps(true);
	    layout.setAutoCreateContainerGaps(true);
	    
	    GroupLayout.ParallelGroup h1a = layout.createParallelGroup(GroupLayout.Alignment.LEADING);
	    h1a.addComponent(lockSizeLabel);
	    h1a.addComponent(serverIPLabel);
	    h1a.addComponent(cellAddrLabel);
	    
	    GroupLayout.ParallelGroup h1b = layout.createParallelGroup(GroupLayout.Alignment.LEADING);
	    h1b.addComponent(lockSizeChoice);
	    h1b.addComponent(serverIPTextField);
	    h1b.addComponent(cellAddrChoice);
	    
	    GroupLayout.ParallelGroup h1c = layout.createParallelGroup(GroupLayout.Alignment.LEADING);
	    h1c.addComponent(enterSizeButton);
	    h1c.addComponent(enterIPButton);
	    h1c.addComponent(enterAddrButton);
	    
	    GroupLayout.SequentialGroup h1 = layout.createSequentialGroup();
	    h1.addGroup(h1a);
	    h1.addGroup(h1b);
	    h1.addGroup(h1c);
	    
	    GroupLayout.ParallelGroup h2 = layout.createParallelGroup(GroupLayout.Alignment.CENTER);
	    h2.addGroup(h1);
	    h2.addComponent(warningMessageLabel);
	    
	    layout.setHorizontalGroup(h2);
	    
	    layout.linkSize(SwingConstants.HORIZONTAL,new Component[] { enterSizeButton, enterIPButton, enterAddrButton });
	    
	    GroupLayout.ParallelGroup v0 = layout.createParallelGroup(GroupLayout.Alignment.CENTER);
	    v0.addComponent(lockSizeLabel);
	    v0.addComponent(lockSizeChoice);
	    v0.addComponent(enterSizeButton);
	    
	    GroupLayout.ParallelGroup v1 = layout.createParallelGroup(GroupLayout.Alignment.CENTER);
	    v1.addComponent(serverIPLabel);
	    v1.addComponent(serverIPTextField);
	    v1.addComponent(enterIPButton);
	    
	    GroupLayout.ParallelGroup v2 = layout.createParallelGroup(GroupLayout.Alignment.CENTER);
	    v2.addComponent(cellAddrLabel);
	    v2.addComponent(cellAddrChoice);
	    v2.addComponent(enterAddrButton);
	    
	    layout.setVerticalGroup(layout.createSequentialGroup().addGroup(v0).addGroup(v1).addGroup(v2).addComponent(warningMessageLabel));
	    
	    layout.linkSize(SwingConstants.VERTICAL,new Component[] { lockSizeChoice, serverIPTextField, cellAddrChoice });
		
	    try
		{
			UIManager.setLookAndFeel(UIManager.getSystemLookAndFeelClassName());
			SwingUtilities.updateComponentTreeUI(this); 	
		}
		catch (Exception ex){}
	    
		this.setTitle("网络锁重置");
	    this.setBounds(400, 200, 480, 160);
		this.setDefaultCloseOperation(EXIT_ON_CLOSE);
		
		this.setVisible(true);

	}
	
	private void createSizeChoice()
	{
		lockSizeChoice.add(Integer.toString(54));
		lockSizeChoice.add(Integer.toString(216));
	}
	
	public String getSizeChoice()
	{
		return lockSizeChoice.getSelectedItem().trim();
	}
	
	public String getIPField()
	{
		return serverIPTextField.getText().trim(); 
	}
	
	public String getAddrChoice()
	{
		return cellAddrChoice.getSelectedItem().trim();
	}
	
	public void setWarningMessage(String message)
	{ 
		warningMessageLabel.setText(message);
	}
	
	public void addAddressItem(int addr)
	{
		cellAddrChoice.add(Integer.toString(addr));
	}
	
	public void setActionListener(ActionListener listener)
	{
		enterSizeButton.addActionListener(listener);
		enterIPButton.addActionListener(listener);
		enterAddrButton.addActionListener(listener);
	}
	
	public void stateAfterSizeInput()
	{
		lockSizeChoice.setEnabled(false);
		enterSizeButton.setEnabled(false);
		
		serverIPTextField.setEnabled(true);
		enterIPButton.setEnabled(true);
		
		cellAddrChoice.setEnabled(false);
		enterAddrButton.setEnabled(false);
		//warningMessageLabel.setText("");
	}
	
	public void stateAfterIPInput()
	{
		lockSizeChoice.setEnabled(false);
		enterSizeButton.setEnabled(false);
		
		serverIPTextField.setEnabled(false);
		enterIPButton.setEnabled(false);
		
		cellAddrChoice.setEnabled(true);
		enterAddrButton.setEnabled(true);
//		warningMessageLabel.setText("");
	}
	
	
	public void stateInitial()
	{
		lockSizeChoice.setEnabled(true);
		enterSizeButton.setEnabled(true);
		
		serverIPTextField.setEnabled(false);
		serverIPTextField.setText("");
		enterIPButton.setEnabled(false);
		
		cellAddrChoice.setEnabled(false);
		cellAddrChoice.removeAll();
		enterAddrButton.setEnabled(false);
		
		warningMessageLabel.setText("");
	}
	
	public static void main(String[] args)
	{
		ResetFrame aFrame = new ResetFrame();
	}

}
