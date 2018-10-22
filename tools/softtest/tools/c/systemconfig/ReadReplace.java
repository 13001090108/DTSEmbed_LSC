package softtest.tools.c.systemconfig;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.util.LinkedList;
import java.util.List;

public class ReadReplace {
	private final static String REPLACE_FILE = "cpp\\replace.txt";
	public ReadReplace(){
		
	}
	public List<Replaces> initReadReplace(){
		List<Replaces> replaces = new LinkedList<Replaces>();
		File replaceFile = new File(REPLACE_FILE);
		if(replaceFile.exists()){
			try{
				BufferedReader reader = new BufferedReader(new FileReader(replaceFile));
				String readreplace;
				while ((readreplace = reader.readLine()) != null){
					String[] temp = readreplace.split("##");
					if(temp.length > 2 || temp.length < 1)
						continue;
					String replace = temp[0].trim();
					if(temp.length == 1 || temp[1] == null || temp[1].trim().equals("")){
						String  replaceBy = "";
						Replaces repl = new Replaces(replace,replaceBy);
						replaces.add(repl);

					}
					else{
						String  replaceBy = temp[1].trim();
						Replaces repl = new Replaces(replace,replaceBy);
						replaces.add(repl);
					}
				}
			}
			catch (Exception e){
				System.err.println("Error in reading the replace file.");
			}
		}
		return replaces;
	}
}
