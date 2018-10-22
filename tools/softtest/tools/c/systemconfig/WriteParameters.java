package softtest.tools.c.systemconfig;

import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;

public class WriteParameters {
	private final static String CONFIG_FILE = "config\\config.ini";
	private final static String NOTE_PREFIX = "#";
	private final static String ORDER_PREFIX = "-";
	
	public WriteParameters(){
		
	}
	public void writeConfig(String[][] parametersTable){
		File configFile = new File(CONFIG_FILE);
		if(configFile.exists()){
			try{
				PrintWriter out = new PrintWriter(new FileWriter(configFile));
				for(int i = 0; i < parametersTable.length; i++){
					out.println(NOTE_PREFIX + parametersTable[i][2]);
					if(parametersTable[i][1].equals("")){
						out.println(ORDER_PREFIX + parametersTable[i][3]);
					}else{
						out.println(ORDER_PREFIX + parametersTable[i][1] + " " + parametersTable[i][3]);
					}
					out.println();
				}
				out.close();
			}
			catch (Exception e){
				System.err.println("Error in writing the config file.");
			}
		}
	}
}
