package softtest.tools.c.systemconfig;

import java.util.LinkedList;
import java.util.List;

import javax.swing.table.AbstractTableModel;

public class RTableModel extends AbstractTableModel{
    private static final long serialVersionUID = 1L;
	
	private static String[][] replacesTable;
	
	private static int number;
	
	private final static String[] columnNames = {"ÐòºÅ" ,"Ìæ»»Ç°" ,"Ìæ»»ºó"};
	
	public RTableModel(){
		List<Replaces> replaces = new LinkedList<Replaces>();
		ReadReplace readrep = new ReadReplace();
		replaces = readrep.initReadReplace();
		number = replaces.size();
		replacesTable = new String[number][3];
		for(int i = 0; i < number; i++){
			replacesTable[i][0] = Integer.toString(i+1);
			replacesTable[i][1] = replaces.get(i).replace;
			replacesTable[i][2] = replaces.get(i).replaceBy;
		}
	}
	public RTableModel(String addStr){
		number = replacesTable.length;
		String[][] tempTable = new String[number+1][3];
		for(int i = 0; i < replacesTable.length; i++){
			for(int j = 0; j < 3; j++){
				tempTable[i][j] = replacesTable[i][j];
			}
		}
		int position = addStr.trim().indexOf("##");
		if(position != -1){
			tempTable[number][0] = Integer.toString(number+1);
			tempTable[number][1] = addStr.substring(0 , position);
			tempTable[number][2] = addStr.substring(position+2).trim();
		}
		replacesTable = tempTable;
	}
	public RTableModel(int rowNumber){
		number = replacesTable.length;
		if(number != 0){
			String[][] tempTable = new String[number-1][3];
			for(int i = 0; i < rowNumber; i++){
				for(int j = 0; j < 3; j++){
					tempTable[i][j] = replacesTable[i][j];
				}
			}
			if((number-1) > rowNumber){
				for(int i = rowNumber; i < number-1; i++){
					tempTable[i][0] = Integer.toString(i+1);
					tempTable[i][1] = replacesTable[i+1][1];
					tempTable[i][2] = replacesTable[i+1][2];
				}
			}
			replacesTable = tempTable;
		}
	}
	public int getColumnCount(){
		return columnNames.length;
	}
	public int getRowCount(){
		return replacesTable.length;
	}
	public String getValueAt(int r, int c){
		return replacesTable[r][c];
	}
	public void setValueAt(Object newValue, int r, int c){
		replacesTable[r][c] = newValue.toString();
	}
	public String getColumnName(int c){
		return columnNames[c];
	}
	public boolean isCellEditable(int r, int c){
		return (c == 1 || c == 2);
	}
	public String[][] getReplacesTable(){
		return replacesTable;
	}
}
