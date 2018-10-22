package softest.registery.file.resetAuth;

import java.awt.Component;
import java.awt.Container;
import java.awt.event.ActionListener;

import javax.swing.GroupLayout;
import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JTextField;
import javax.swing.SwingConstants;
import javax.swing.SwingUtilities;
import javax.swing.UIManager;

public class ResetAuthFrame extends JFrame
{
	private JLabel requestLabel;

	private JTextField requestFiled;

	// private JButton enterSNButton;

	private JLabel respondLabel;

	private JTextField respondFiled;

	// private JButton enterNumButton;

	private JButton enter;

	public ResetAuthFrame()
	{
		requestLabel = new JLabel("重置请求码：");
		requestFiled = new JTextField();
		// enterSNButton = new JButton("输入SN");
		// enterSNButton.setActionCommand("SN");
		requestFiled.setFocusable(true);

		respondLabel = new JLabel("重置响应码：");
		respondFiled = new JTextField();
		respondFiled.setEditable(false);
		// enterNumButton = new JButton("输入次数");
		// enterNumButton.setActionCommand("NUM");

		enter = new JButton("生成响应码");
		enter.setActionCommand("enter");

		Container c = this.getContentPane();
		GroupLayout layout = new GroupLayout(c);
		c.setLayout(layout);

		layout.setAutoCreateGaps(true);
		layout.setAutoCreateContainerGaps(true);

		GroupLayout.ParallelGroup h1a = layout
				.createParallelGroup(GroupLayout.Alignment.LEADING);
		h1a.addComponent(requestLabel);
		h1a.addComponent(respondLabel);

		GroupLayout.ParallelGroup h1b = layout
				.createParallelGroup(GroupLayout.Alignment.LEADING);
		h1b.addComponent(requestFiled);
		h1b.addComponent(respondFiled);
		// h1b.addComponent(enter);

		/*
		 * GroupLayout.ParallelGroup h1c =
		 * layout.createParallelGroup(GroupLayout.Alignment.LEADING);
		 * h1c.addComponent(enterSNButton); h1c.addComponent(enterNumButton);
		 */

		GroupLayout.SequentialGroup h1 = layout.createSequentialGroup();
		h1.addGroup(h1a);
		h1.addGroup(h1b);
		// h1.addGroup(h1c);

		GroupLayout.ParallelGroup h2 = layout
				.createParallelGroup(GroupLayout.Alignment.TRAILING);
		h2.addGroup(h1);
		h2.addComponent(enter);

		layout.setHorizontalGroup(h2);

		// layout.linkSize(SwingConstants.HORIZONTAL,new Component[] {
		// enterSNButton, enterNumButton });

		GroupLayout.ParallelGroup v1 = layout
				.createParallelGroup(GroupLayout.Alignment.CENTER);
		v1.addComponent(requestLabel);
		v1.addComponent(requestFiled);
		// v1.addComponent(enterSNButton);

		GroupLayout.ParallelGroup v2 = layout
				.createParallelGroup(GroupLayout.Alignment.CENTER);
		v2.addComponent(respondLabel);
		v2.addComponent(respondFiled);
		// v2.addComponent(enterNumButton);

		layout.setVerticalGroup(layout.createSequentialGroup().addGroup(v1)
				.addGroup(v2).addComponent(enter));

		layout.linkSize(SwingConstants.VERTICAL, new Component[] {
				requestFiled, respondFiled });

		try
		{
			UIManager.setLookAndFeel(UIManager.getSystemLookAndFeelClassName());
			SwingUtilities.updateComponentTreeUI(this);
		}
		catch (Exception ex)
		{
		}

		this.setTitle("DTS重置码生成器");
		this.setBounds(400, 200, 320, 130);
		this.setResizable(false);
		this.setDefaultCloseOperation(EXIT_ON_CLOSE);

		// this.setVisible(true);

	}

	public void addActionLisener(ActionListener listener)
	{
		// enterSNButton.addActionListener(listener);
		// enterNumButton.addActionListener(listener);
		enter.addActionListener(listener);
	}

	public String getReqField()
	{
		return requestFiled.getText().trim();
	}

	public void setRespondField(String meg)
	{
		respondFiled.setText(meg);
	}

	/*
	 * public void stateInitial() { requestFiled.setText("");
	 * requestFiled.setEnabled(true); requestFiled.setFocusable(true);
	 * respondFiled.setText(""); respondFiled.setEnabled(false); }
	 * 
	 * public void stateAfterEnterAction() { requestFiled.setEnabled(false); //
	 * enterSNButton.setEnabled(false); requestFiled.setEnabled(false); //
	 * enterNumButton.setEnabled(false); }
	 */

}
