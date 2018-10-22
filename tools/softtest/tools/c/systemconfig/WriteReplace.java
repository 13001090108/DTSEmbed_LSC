package softtest.tools.c.systemconfig;

import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;

public class WriteReplace {
	private final static String REPLACE_FILE = "cpp\\replace.txt";
	public WriteReplace(){
		
	}
	public void writeReplaces(String[][] replacesTable){
		File replaceFile = new File(REPLACE_FILE);
		if(replaceFile.exists()){
			try{
				PrintWriter out = new PrintWriter(new FileWriter(replaceFile));
				for(int i = 0; i < replacesTable.length; i++){
					if(replacesTable[i][2].equals("")){
						out.println(replacesTable[i][1] + "##");
					}else{
						out.println(replacesTable[i][1] + "##" + replacesTable[i][2]);
					}
				}
				out.close();
			}
			catch(Exception e){
				System.err.println("Error in writing the replace file.");
			}
		}
	}
}

