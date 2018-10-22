package softtest.tools.c.systemconfig;

import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;

public class WriteDefines {
	private final static String DEFINES_FILE = "cpp\\defines.txt";
	public WriteDefines(){
		
	}
	public void writeDefines(String[][] definesTable, String[] notes){
		File definesFile = new File(DEFINES_FILE);
		if(definesFile.exists()){
			try{
				PrintWriter out = new PrintWriter(new FileWriter(definesFile));
				if(notes.length > 0){
					for(int i = 0; i < notes.length; i++){
						out.println(notes[i]);
					}
					out.println();
				}
				for(int i = 0; i < definesTable.length; i++){
					if(definesTable[i][2].equals("")){
						out.println("#define " + definesTable[i][1]);
					}else{
						out.println("#define " + definesTable[i][1] + " " + definesTable[i][2]);
					}
				}
				out.close();
			}
			catch(Exception e){
				System.err.println("Error in writing the defines file.");
			}
		}
	}
}
