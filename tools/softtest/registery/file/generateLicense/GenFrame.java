package softtest.registery.file.generateLicense;

import java.awt.Component;
import java.awt.Container;
import java.awt.event.ActionListener;

import javax.swing.GroupLayout;
import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;

import javax.swing.JTextField;
import javax.swing.SwingConstants;

public class GenFrame extends JFrame
{
	private JLabel serialNumLabel;

	private JTextField serialNumField;

	private JLabel authenNumLabel;

	private JTextField authenNumField;

	private JButton enter;

	public GenFrame()
	{
		serialNumLabel = new JLabel("序列号：");
		serialNumField = new JTextField();

		serialNumField.setFocusable(true);

		authenNumLabel = new JLabel("许可次数：");
		authenNumField = new JTextField();

		enter = new JButton("生成许可文件");
		enter.setActionCommand("enter");

		Container c = this.getContentPane();
		GroupLayout layout = new GroupLayout(c);
		c.setLayout(layout);

		layout.setAutoCreateGaps(true);
		layout.setAutoCreateContainerGaps(true);

		GroupLayout.ParallelGroup h1a = layout
				.createParallelGroup(GroupLayout.Alignment.LEADING);
		h1a.addComponent(serialNumLabel);
		h1a.addComponent(authenNumLabel);

		GroupLayout.ParallelGroup h1b = layout
				.createParallelGroup(GroupLayout.Alignment.LEADING);
		h1b.addComponent(serialNumField);
		h1b.addComponent(authenNumField);

		GroupLayout.SequentialGroup h1 = layout.createSequentialGroup();
		h1.addGroup(h1a);
		h1.addGroup(h1b);

		GroupLayout.ParallelGroup h2 = layout
				.createParallelGroup(GroupLayout.Alignment.TRAILING);
		h2.addGroup(h1);
		h2.addComponent(enter);

		layout.setHorizontalGroup(h2);

		GroupLayout.ParallelGroup v1 = layout
				.createParallelGroup(GroupLayout.Alignment.CENTER);
		v1.addComponent(serialNumLabel);
		v1.addComponent(serialNumField);

		GroupLayout.ParallelGroup v2 = layout
				.createParallelGroup(GroupLayout.Alignment.CENTER);
		v2.addComponent(authenNumLabel);
		v2.addComponent(authenNumField);

		layout.setVerticalGroup(layout.createSequentialGroup().addGroup(v1)
				.addGroup(v2).addComponent(enter));

		layout.linkSize(SwingConstants.VERTICAL, new Component[] {
				serialNumField, authenNumField });

		this.setTitle("DTS许可文件生成器");
		this.setBounds(400, 200, 380, 125);
		this.setResizable(false);
		this.setDefaultCloseOperation(EXIT_ON_CLOSE);

	}

	public void addActionLisener(ActionListener listener)
	{
		enter.addActionListener(listener);
	}

	public String getSNField()
	{
		return serialNumField.getText().trim();
	}

	public String getNumField()
	{
		return authenNumField.getText().trim();
	}

	public void stateInitial()
	{
		serialNumField.setEnabled(true);
		serialNumField.setFocusable(true);
		authenNumField.setEnabled(true);

		serialNumField.setText("");
		authenNumField.setText("");

	}

	public void stateAfterInput()
	{
		serialNumField.setEnabled(false);
		authenNumField.setEnabled(false);
	}

	public void stateErrorInput()
	{
		serialNumField.setEnabled(true);
		serialNumField.setFocusable(true);
		authenNumField.setEnabled(true);
	}

}
