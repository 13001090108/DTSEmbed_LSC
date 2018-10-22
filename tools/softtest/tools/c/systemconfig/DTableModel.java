package softtest.tools.c.systemconfig;

import java.util.LinkedList;
import java.util.List;

import javax.swing.table.AbstractTableModel;

public class DTableModel extends AbstractTableModel{
	private static final long serialVersionUID = 1L;
	
	private static String[][] definesTable;
	
	private static String[] notes;
	
	private static int number;
	
	private final static String[] columnNames = {"ÐòºÅ" ,"Ìæ»»Ç°" ,"Ìæ»»ºó"};
	
	public DTableModel(){
		List<Replaces> defines = new LinkedList<Replaces>();
		ReadDefines readdef = new ReadDefines();
		defines = readdef.initReadDefines();
		notes = readdef.getNotes();
		number = defines.size();
		definesTable = new String[number][3];
		for(int i = 0; i < number; i++){
			definesTable[i][0] = Integer.toString(i+1);
			definesTable[i][1] = defines.get(i).replace;
			definesTable[i][2] = defines.get(i).replaceBy;
		}
	}
	public DTableModel(String addStr){//Ìí¼Ó
		number = definesTable.length;
		String[][] tempTable = new String[number+1][3];
		for(int i = 0; i < definesTable.length; i++){
			for(int j = 0; j < 3; j++){
				tempTable[i][j] = definesTable[i][j];
			}
		}
		int position = ReadDefines.getposition(addStr.trim());
		tempTable[number][0] = Integer.toString(number+1);
		tempTable[number][1] = addStr.substring(0, position+1);
		tempTable[number][2] = addStr.substring(position+1).trim();
		definesTable = tempTable;
	}
	public DTableModel(int rowNumber){//É¾³ý
		number = definesTable.length;
		if(number != 0){
			String[][] tempTable = new String[number-1][3];
			for(int i = 0; i < rowNumber; i++){
				for(int j = 0; j < 3; j++){
					tempTable[i][j] = definesTable[i][j];
				}
			}
			if((number-1) > rowNumber){
				for(int i = rowNumber; i < number-1; i++){
					tempTable[i][0] = Integer.toString(i+1);
					tempTable[i][1] = definesTable[i+1][1];
					tempTable[i][2] = definesTable[i+1][2];
				}
			}
			definesTable = tempTable;
		}
	}
	public int getColumnCount(){
		return columnNames.length;
	}
	public int getRowCount(){
		return definesTable.length;
	}
	public String getValueAt(int r, int c){
		return definesTable[r][c];
	}
	public void setValueAt(Object newValue, int r, int c){
		definesTable[r][c] = newValue.toString();
	}
	public String getColumnName(int c){
		return columnNames[c];
	}
	public boolean isCellEditable(int r, int c){
		return (c == 1 || c == 2);
	}
	public String[][] getDefinesTable(){
		return definesTable;
	}
	public String[] getNotes(){
		if(notes != null){
			return notes;
		}else{
			return null;
		}
	}
}
