package softtest.tools.c.systemconfig;

import java.util.LinkedList;
import java.util.List;

import javax.swing.table.AbstractTableModel;

public class CTableModel extends AbstractTableModel{
	
	private static final long serialVersionUID = 1L;
	
	private static String[][] parametersTable;
	
	private static int number;
	
	private final static String[] columnNames = {"序号" ,"参数名称" ,"参数描述" ,"参数值"};
	
	public CTableModel(){
		List<Parameters> parameters = new LinkedList<Parameters>();
		ReadParameters readpara = new ReadParameters();
		parameters = readpara.initReadConfig();
		number = parameters.size();
		parametersTable = new String[number][4];
		for(int i = 0; i < number; i++){
			parametersTable[i][0] = Integer.toString(i+1);
			parametersTable[i][1] = parameters.get(i).name;
			parametersTable[i][2] = parameters.get(i).description;
			parametersTable[i][3] = parameters.get(i).value.toString();
		}
	}
	public int getColumnCount(){
		return columnNames.length;
	}
	public int getRowCount(){
		return parametersTable.length;
	}
	public String getValueAt(int r, int c){
		return parametersTable[r][c];
	}
	public void setValueAt(Object newValue, int r, int c){
		parametersTable[r][c] = newValue.toString();
	}
	public String getColumnName(int c){
		return columnNames[c];
	}
	public boolean isCellEditable(int r, int c){
		return c == 3;
	}
	public String[][] getParametersTable(){
		return parametersTable;
	}
}
