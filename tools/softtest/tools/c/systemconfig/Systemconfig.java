package softtest.tools.c.systemconfig;

import javax.swing.JOptionPane;
import javax.swing.SwingUtilities;
import javax.swing.JPanel;
import javax.swing.JFrame;
import javax.swing.JTabbedPane;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Rectangle;
import java.awt.Toolkit;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.JButton;
import javax.swing.table.TableCellEditor;
import javax.swing.table.TableColumn;
import javax.swing.table.TableModel;

public class Systemconfig extends JFrame {

	private static final long serialVersionUID = 1L;

	private JPanel jContentPane = null;

	private JTabbedPane jTabbedPane = null;

	private JPanel jPanel = null;
	
	private JPanel jPanel1 = null;
	
	private JPanel jPanel2 = null;

	private JScrollPane jScrollPane = null;

	private JTable jTable = null;

	private JButton jButton = null;
	
	private static String[][] parametersTable;
	
	private static String[][] definesTable;
	
	private static String[][] replacesTable;
	
	private static String[] notes;
	
	private TableModel cmodel;  //  @jve:decl-index=0:
	
	private TableModel dmodel;
	
	private TableModel rmodel;
	
	private TableCellEditor tableCellEditorConfig = null;
	
	private TableCellEditor tableCellEditorDefines = null;
	
	private TableCellEditor tableCellEditorReplace = null;
	
	private static int height;
	
	private static int width;

	private JScrollPane jScrollPane1 = null;

	private JTable jTable1 = null;

	private JButton jButton1 = null;

	private JButton jButton2 = null;

	private JButton jButton3 = null;

	private JScrollPane jScrollPane2 = null;

	private JTable jTable2 = null;

	private JButton jButton4 = null;

	private JButton jButton5 = null;

	private JButton jButton6 = null;

	/**
	 * This method initializes jTabbedPane	
	 * 	
	 * @return javax.swing.JTabbedPane	
	 */
	private JTabbedPane getJTabbedPane() {
		if (jTabbedPane == null) {
			jTabbedPane = new JTabbedPane();
			jTabbedPane.setBounds(new Rectangle(0, 0, 229*width/288, 119*height/288));
			jTabbedPane.addTab("系统配置", null, getJPanel(), null);
			jTabbedPane.addTab("宏替换（源和工程测试模式）", null, getJPanel1(), null);
			jTabbedPane.addTab("宏替换（中间文件测试模式）", null, getJPanel2(), null);
//			jTabbedPane.setSelectedIndex(jTabbedPane.getTabCount() - 1);
		}
		return jTabbedPane;
	}

	/**
	 * This method initializes jPanel	
	 * 	
	 * @return javax.swing.JPanel	
	 */
	private JPanel getJPanel() {
		if (jPanel == null) {
			jPanel = new JPanel();
			jPanel.setLayout(null);
			jPanel.add(getJScrollPane(), null);
			jPanel.add(getJButton(), null);
		}
		return jPanel;
	}
	
	/**
	 * This method initializes jPanel1	
	 * 	
	 * @return javax.swing.JPanel	
	 */
	private JPanel getJPanel1() {
		if (jPanel1 == null) {
			jPanel1 = new JPanel();
			jPanel1.setLayout(null);
			jPanel1.add(getJScrollPane1(), null);
			jPanel1.add(getJButton1(), null);
			jPanel1.add(getJButton2(), null);
			jPanel1.add(getJButton3(), null);
		}
		return jPanel1;
	}
	
	/**
	 * This method initializes jPanel2	
	 * 	
	 * @return javax.swing.JPanel	
	 */
	private JPanel getJPanel2() {
		if (jPanel2 == null) {
			jPanel2 = new JPanel();
			jPanel2.setLayout(null);
			jPanel2.add(getJScrollPane2(), null);
			jPanel2.add(getJButton4(), null);
			jPanel2.add(getJButton5(), null);
			jPanel2.add(getJButton6(), null);
		}
		return jPanel2;
	}

	/**
	 * This method initializes jScrollPane	
	 * 	
	 * @return javax.swing.JScrollPane	
	 */
	private JScrollPane getJScrollPane() {
		if (jScrollPane == null) {
			jScrollPane = new JScrollPane();
			jScrollPane.setBounds(new Rectangle(0, 0, 57*width/72, height/3));
			jScrollPane.setViewportView(getJTable());
		}
		return jScrollPane;
	}

	/**
	 * This method initializes jTable	
	 * 	
	 * @return javax.swing.JTable	
	 */
	private JTable getJTable() {
		if (jTable == null) {
			cmodel = new CTableModel();
			jTable = new JTable(cmodel);
			jTable.setRowHeight(height/40);
			TableColumn numberColumn = jTable.getColumnModel().getColumn(0);
			TableColumn nameColumn = jTable.getColumnModel().getColumn(1);
			TableColumn descriptionColumn = jTable.getColumnModel().getColumn(2);
			TableColumn valueColumn = jTable.getColumnModel().getColumn(3);
			numberColumn.setPreferredWidth(width/18);
			nameColumn.setPreferredWidth(width/9);
			descriptionColumn.setPreferredWidth(width/2);
			valueColumn.setPreferredWidth(width/8);
			jTable.addPropertyChangeListener(new PropertyChangeListener(){
				public void propertyChange(PropertyChangeEvent event){
					int r = jTable.getSelectedRow();
					int c = jTable.getSelectedColumn();
					if((r >= 0) && (c >= 0)){
						tableCellEditorConfig = jTable.getCellEditor(r, c);
						jTable.getValueAt(r, c);
						if(event.getNewValue() != null){
							jTable.setValueAt(event.getNewValue(), r, c);
						}
					}
				}
			});
		}
		return jTable;
	}

	/**
	 * This method initializes jButton	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButton() {
		if (jButton == null) {
			jButton = new JButton();
			jButton.setText("保存");
			jButton.setBounds(new Rectangle(16*width/45, 37*height/108, width/15, 25*height/720));
			jButton.addMouseListener(new java.awt.event.MouseAdapter() {
				public void mouseClicked(java.awt.event.MouseEvent e) {
					jButtonMouseClicked(e);
					//System.out.println("mouseClicked()"); // TODO Auto-generated Event stub mouseClicked()
				}
			});
		}
		return jButton;
	}

	/**
	 * This method initializes jScrollPane1	
	 * 	
	 * @return javax.swing.JScrollPane	
	 */
	private JScrollPane getJScrollPane1() {
		if (jScrollPane1 == null) {
			jScrollPane1 = new JScrollPane();
			jScrollPane1.setBounds(new Rectangle(0, 0, 57*width/72, height/3));
			jScrollPane1.setViewportView(getJTable1());
		}
		return jScrollPane1;
	}

	/**
	 * This method initializes jTable1	
	 * 	
	 * @return javax.swing.JTable	
	 */
	private JTable getJTable1() {
		if (jTable1 == null) {
			dmodel = new DTableModel();
			jTable1 = new JTable(dmodel);
			jTable1.setRowHeight(height/40);
			TableColumn numberColumn = jTable1.getColumnModel().getColumn(0);
			TableColumn replaceColumn = jTable1.getColumnModel().getColumn(1);
			TableColumn replaceByColumn = jTable1.getColumnModel().getColumn(2);
			numberColumn.setPreferredWidth(width/18);
			replaceColumn.setPreferredWidth(17*width/72);
			replaceByColumn.setPreferredWidth(width/2);
			jTable1.addPropertyChangeListener(new PropertyChangeListener(){
				public void propertyChange(PropertyChangeEvent event){
					int r = jTable1.getSelectedRow();
					int c = jTable1.getSelectedColumn();
					if((r >= 0) && (c >= 0)){
						tableCellEditorDefines = jTable1.getCellEditor(r, c);
						jTable1.getValueAt(r, c);
						if(event.getNewValue() != null){
							jTable1.setValueAt(event.getNewValue(), r, c);
						}
					}
				}
			});
		}
		return jTable1;
	}

	/**
	 * This method initializes jButton1	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButton1() {
		if (jButton1 == null) {
			jButton1 = new JButton();
			jButton1.setText("保存");
			jButton1.setBounds(new Rectangle(width/5, 37*height/108, width/15, 25*height/720));
			jButton1.addMouseListener(new java.awt.event.MouseAdapter() {
				public void mouseClicked(java.awt.event.MouseEvent e) {
					jButton1MouseClicked(e);
					//System.out.println("mouseClicked()"); // TODO Auto-generated Event stub mouseClicked()
				}
			});
		}
		return jButton1;
	}

	/**
	 * This method initializes jButton2	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButton2() {
		if (jButton2 == null) {
			jButton2 = new JButton();
			jButton2.setText("添加");
			jButton2.setBounds(new Rectangle(16*width/45, 37*height/108, width/15, 25*height/720));
			jButton2.addMouseListener(new java.awt.event.MouseAdapter() {
				public void mouseClicked(java.awt.event.MouseEvent e) {
					jButton2MouseClicked(e);
					//System.out.println("mouseClicked()"); // TODO Auto-generated Event stub mouseClicked()
				}
			});
		}
		return jButton2;
	}

	/**
	 * This method initializes jButton3	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButton3() {
		if (jButton3 == null) {
			jButton3 = new JButton();
			jButton3.setText("删除");
			jButton3.setBounds(new Rectangle(23*width/45, 37*height/108, width/15, 25*height/720));
			jButton3.addMouseListener(new java.awt.event.MouseAdapter() {
				public void mouseClicked(java.awt.event.MouseEvent e) {
					jButton3MouseClicked(e);
					//System.out.println("mouseClicked()"); // TODO Auto-generated Event stub mouseClicked()
				}
			});
		}
		return jButton3;
	}

	/**
	 * This method initializes jScrollPane2	
	 * 	
	 * @return javax.swing.JScrollPane	
	 */
	private JScrollPane getJScrollPane2() {
		if (jScrollPane2 == null) {
			jScrollPane2 = new JScrollPane();
			jScrollPane2.setBounds(new Rectangle(0, 0, 57*width/72, height/3));
			jScrollPane2.setViewportView(getJTable2());
		}
		return jScrollPane2;
	}

	/**
	 * This method initializes jTable2	
	 * 	
	 * @return javax.swing.JTable	
	 */
	private JTable getJTable2() {
		if (jTable2 == null) {
			rmodel = new RTableModel();
			jTable2 = new JTable(rmodel);
			jTable2.setRowHeight(height/40);
			TableColumn numberColumn = jTable2.getColumnModel().getColumn(0);
			TableColumn replaceColumn = jTable2.getColumnModel().getColumn(1);
			TableColumn replaceByColumn = jTable2.getColumnModel().getColumn(2);
			numberColumn.setPreferredWidth(width/18);
			replaceColumn.setPreferredWidth(17*width/72);
			replaceByColumn.setPreferredWidth(width/2);
			jTable2.addPropertyChangeListener(new PropertyChangeListener(){
				public void propertyChange(PropertyChangeEvent event){
					int r = jTable2.getSelectedRow();
					int c = jTable2.getSelectedColumn();
					if((r >= 0) && (c >= 0)){
						tableCellEditorReplace = jTable2.getCellEditor(r, c);
						jTable2.getValueAt(r, c);
						if(event.getNewValue() != null){
							jTable2.setValueAt(event.getNewValue(), r, c);
						}
					}
				}
			});
		}
		return jTable2;
	}

	/**
	 * This method initializes jButton4	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButton4() {
		if (jButton4 == null) {
			jButton4 = new JButton();
			jButton4.setText("保存");
			jButton4.setBounds(new Rectangle(width/5, 37*height/108, width/15, 25*height/720));
			jButton4.addMouseListener(new java.awt.event.MouseAdapter() {
				public void mouseClicked(java.awt.event.MouseEvent e) {
					jButton4MouseClicked(e);
					//System.out.println("mouseClicked()"); // TODO Auto-generated Event stub mouseClicked()
				}
			});
		}
		return jButton4;
	}

	/**
	 * This method initializes jButton5	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButton5() {
		if (jButton5 == null) {
			jButton5 = new JButton();
			jButton5.setText("添加");
			jButton5.setBounds(new Rectangle(16*width/45, 37*height/108, width/15, 25*height/720));
			jButton5.addMouseListener(new java.awt.event.MouseAdapter() {
				public void mouseClicked(java.awt.event.MouseEvent e) {
					jButton5MouseClicked(e);
					//System.out.println("mouseClicked()"); // TODO Auto-generated Event stub mouseClicked()
				}
			});
		}
		return jButton5;
	}

	/**
	 * This method initializes jButton6	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButton6() {
		if (jButton6 == null) {
			jButton6 = new JButton();
			jButton6.setText("删除");
			jButton6.setBounds(new Rectangle(23*width/45, 37*height/108, width/15, 25*height/720));
			jButton6.addMouseListener(new java.awt.event.MouseAdapter() {
				public void mouseClicked(java.awt.event.MouseEvent e) {
					jButton6MouseClicked(e);
					//System.out.println("mouseClicked()"); // TODO Auto-generated Event stub mouseClicked()
				}
			});
		}
		return jButton6;
	}

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		// TODO 自动生成方法存根
		SwingUtilities.invokeLater(new Runnable() {
			public void run() {
				Systemconfig thisClass = new Systemconfig();
				thisClass.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
				thisClass.setVisible(true);
			}
		});
	}

	/**
	 * This is the default constructor
	 */
	public Systemconfig() {
		super();
		initialize();
	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		Dimension screenSize = Toolkit.getDefaultToolkit().getScreenSize();
		height = screenSize.height;
		width = screenSize.width;
		this.setSize(4*width/5, 4*height/9);
		this.setContentPane(getJContentPane());
		this.setTitle("配置设置");
	}

	/**
	 * This method initializes jContentPane
	 * 
	 * @return javax.swing.JPanel
	 */
	private JPanel getJContentPane() {
		if (jContentPane == null) {
			jContentPane = new JPanel();
			jContentPane.setLayout(null);
			jContentPane.setBackground(new Color(208, 207, 207));
			jContentPane.add(getJTabbedPane(), null);
		}
		return jContentPane;
	}
	
	private void jButtonMouseClicked(java.awt.event.MouseEvent e) {
		if(tableCellEditorConfig == null){
			parametersTable = new String[cmodel.getRowCount()][4];
			parametersTable = ((CTableModel)cmodel).getParametersTable();
			WriteParameters writeParameters = new WriteParameters();
			writeParameters.writeConfig(parametersTable);
		}else{
			tableCellEditorConfig.stopCellEditing();
			parametersTable = new String[cmodel.getRowCount()][4];
			parametersTable = ((CTableModel)cmodel).getParametersTable();
			WriteParameters writeParameters = new WriteParameters();
			writeParameters.writeConfig(parametersTable);
		}
	}
	
	private void jButton1MouseClicked(java.awt.event.MouseEvent e) {
		if(tableCellEditorDefines == null){
			definesTable = new String[dmodel.getRowCount()][3];
			definesTable = ((DTableModel)dmodel).getDefinesTable();
			notes = ((DTableModel)dmodel).getNotes();
			WriteDefines writeDefines = new WriteDefines();
			writeDefines.writeDefines(definesTable, notes);
		}else{
			tableCellEditorDefines.stopCellEditing();
			definesTable = new String[dmodel.getRowCount()][3];
			definesTable = ((DTableModel)dmodel).getDefinesTable();
			notes = ((DTableModel)dmodel).getNotes();
			WriteDefines writeDefines = new WriteDefines();
			writeDefines.writeDefines(definesTable, notes);
		}
	}
	
	private void jButton2MouseClicked(java.awt.event.MouseEvent e) {
		String addStr = JOptionPane.showInputDialog("请输入替换前和替换后的字串，以括号或空格分隔");
		dmodel = new DTableModel(addStr);
		jTable1 = new JTable(dmodel);
		jTable1.setRowHeight(height/40);
		TableColumn numberColumn = jTable1.getColumnModel().getColumn(0);
		TableColumn replaceColumn = jTable1.getColumnModel().getColumn(1);
		TableColumn replaceByColumn = jTable1.getColumnModel().getColumn(2);
		numberColumn.setPreferredWidth(width/18);
		replaceColumn.setPreferredWidth(17*width/72);
		replaceByColumn.setPreferredWidth(width/2);
		jTable1.addPropertyChangeListener(new PropertyChangeListener(){
			public void propertyChange(PropertyChangeEvent event){
				int r = jTable1.getSelectedRow();
				int c = jTable1.getSelectedColumn();
				if((r >= 0) && (c >= 0)){
					tableCellEditorDefines = jTable1.getCellEditor(r, c);
					jTable1.getValueAt(r, c);
					if(event.getNewValue() != null){
						jTable1.setValueAt(event.getNewValue(), r, c);
					}
				}
			}
		});
		jScrollPane1.setViewportView(jTable1);
	}
	
    private void jButton3MouseClicked(java.awt.event.MouseEvent e) {
		int selected = jTable1.getSelectedRow();
		dmodel = new DTableModel(selected);
		jTable1 = new JTable(dmodel);
		jTable1.setRowHeight(height/40);
		TableColumn numberColumn = jTable1.getColumnModel().getColumn(0);
		TableColumn replaceColumn = jTable1.getColumnModel().getColumn(1);
		TableColumn replaceByColumn = jTable1.getColumnModel().getColumn(2);
		numberColumn.setPreferredWidth(width/18);
		replaceColumn.setPreferredWidth(17*width/72);
		replaceByColumn.setPreferredWidth(width/2);
		jTable1.addPropertyChangeListener(new PropertyChangeListener(){
			public void propertyChange(PropertyChangeEvent event){
				int r = jTable1.getSelectedRow();
				int c = jTable1.getSelectedColumn();
				if((r >= 0) && (c >= 0)){
					tableCellEditorDefines = jTable1.getCellEditor(r, c);
					jTable1.getValueAt(r, c);
					if(event.getNewValue() != null){
						jTable1.setValueAt(event.getNewValue(), r, c);
					}
				}
			}
		});
		jScrollPane1.setViewportView(jTable1);
	}
	
	private void jButton4MouseClicked(java.awt.event.MouseEvent e) {
		if(tableCellEditorReplace == null){
			replacesTable = new String[rmodel.getRowCount()][3];
			replacesTable = ((RTableModel)rmodel).getReplacesTable();
			WriteReplace writeReplace = new WriteReplace();
			writeReplace.writeReplaces(replacesTable);
		}else{
			tableCellEditorReplace.stopCellEditing();
			replacesTable = new String[rmodel.getRowCount()][3];
			replacesTable = ((RTableModel)rmodel).getReplacesTable();
			WriteReplace writeReplace = new WriteReplace();
			writeReplace.writeReplaces(replacesTable);
		}
	}
	
    private void jButton5MouseClicked(java.awt.event.MouseEvent e) {
		String addStr = JOptionPane.showInputDialog("请输入替换前和替换后的字串，以##分隔");
		rmodel = new RTableModel(addStr);
		jTable2 = new JTable(rmodel);
		jTable2.setRowHeight(height/40);
		TableColumn numberColumn = jTable2.getColumnModel().getColumn(0);
		TableColumn replaceColumn = jTable2.getColumnModel().getColumn(1);
		TableColumn replaceByColumn = jTable2.getColumnModel().getColumn(2);
		numberColumn.setPreferredWidth(width/18);
		replaceColumn.setPreferredWidth(17*width/72);
		replaceByColumn.setPreferredWidth(width/2);
		jTable2.addPropertyChangeListener(new PropertyChangeListener(){
			public void propertyChange(PropertyChangeEvent event){
				int r = jTable2.getSelectedRow();
				int c = jTable2.getSelectedColumn();
				if((r >= 0) && (c >= 0)){
					tableCellEditorReplace = jTable2.getCellEditor(r, c);
					jTable2.getValueAt(r, c);
					if(event.getNewValue() != null){
						jTable2.setValueAt(event.getNewValue(), r, c);
					}
				}
			}
		});
		jScrollPane2.setViewportView(jTable2);
	}
    
    private void jButton6MouseClicked(java.awt.event.MouseEvent e) {
    	int selected = jTable2.getSelectedRow();
    	rmodel = new RTableModel(selected);
		jTable2 = new JTable(rmodel);
		jTable2.setRowHeight(height/40);
		TableColumn numberColumn = jTable2.getColumnModel().getColumn(0);
		TableColumn replaceColumn = jTable2.getColumnModel().getColumn(1);
		TableColumn replaceByColumn = jTable2.getColumnModel().getColumn(2);
		numberColumn.setPreferredWidth(width/18);
		replaceColumn.setPreferredWidth(17*width/72);
		replaceByColumn.setPreferredWidth(width/2);
		jTable2.addPropertyChangeListener(new PropertyChangeListener(){
			public void propertyChange(PropertyChangeEvent event){
				int r = jTable2.getSelectedRow();
				int c = jTable2.getSelectedColumn();
				if((r >= 0) && (c >= 0)){
					tableCellEditorReplace = jTable2.getCellEditor(r, c);
					jTable2.getValueAt(r, c);
					if(event.getNewValue() != null){
						jTable2.setValueAt(event.getNewValue(), r, c);
					}
				}
			}
		});
		jScrollPane2.setViewportView(jTable2);
	}

}  //  @jve:decl-index=0:visual-constraint="87,63"
