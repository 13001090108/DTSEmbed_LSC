package softtest.tools.c.systemconfig;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.util.LinkedList;
import java.util.List;

public class ReadDefines {
	private final static String DEFINES_FILE = "cpp\\defines.txt";
	private static String[] notes;
	public ReadDefines(){
		
	}
	public List<Replaces>initReadDefines(){
		List<Replaces> replaces = new LinkedList<Replaces>();
		File definesFile = new File(DEFINES_FILE);
		if(definesFile.exists()){
			try{
				BufferedReader reader = new BufferedReader(new FileReader(definesFile));
				String readdefines;
				List<String> preNotes = new LinkedList<String>();
				boolean isNotes = false;
				while ((readdefines = reader.readLine()) != null){
					if(readdefines.trim().startsWith("/**")){
						isNotes = true;
					}
					if(readdefines.trim().startsWith("*/")){
						preNotes.add(readdefines);
						isNotes = false;
						continue;
					}
					if(isNotes){
						preNotes.add(readdefines);
					}else{
						if(readdefines.startsWith("#define")){
							readdefines = readdefines.substring(7).trim();
							String[] temp = readdefines.split(" ");
							String replace;
							String replaceBy;
							if(temp.length == 1){
								replace = temp[0].trim();
								replaceBy = "";
								Replaces repl = new Replaces(replace,replaceBy);
								replaces.add(repl);
							}
							if(temp.length  == 2){
								replace = temp[0].trim();
								replaceBy = temp[1].trim();
								Replaces repl = new Replaces(replace,replaceBy);
								replaces.add(repl);
							}
							if(temp.length > 2){
								int position = getposition(readdefines);
								if(position == -1){
									continue;
								}
								replace = readdefines.substring(0, position + 1);
								replaceBy = readdefines.substring(position + 1).trim();
								Replaces repl = new Replaces(replace,replaceBy);
								replaces.add(repl);
							}else{
								continue;
							}
						}
					}
				}
				if(preNotes.size() > 0){
					notes = new String[preNotes.size()];
					for(int i = 0; i < preNotes.size(); i++){
						notes[i] = preNotes.get(i);
					}
				}
			}
			catch (Exception e){
				System.err.println("Error in reading the defines file.");
			}
		}
		return replaces;
	}
	public static int getposition(String readdefines){//Æ¥ÅäÀ¨ºÅ
		int position = readdefines.indexOf("(");
		if(position == -1){
			position = readdefines.indexOf(" ");
			return position;
		}else{
			readdefines = readdefines.substring(position + 1);
			position++;
			int count = 1;
			while(count != 0){
				if(readdefines.startsWith("(")){
					count++;
					readdefines = readdefines.substring(1);
					position++;
				}
				else{
					if(readdefines.startsWith(")")){
						count--;
						if(count != 0){
							readdefines = readdefines.substring(1);
							position++;
						}
					}else{
						readdefines = readdefines.substring(1);
						position++;
					}
				} 
			}
			return position;
		}
	}
	public String[] getNotes(){
		if(notes != null){
			return notes;
		}else{
			return null;
		}
	}
}