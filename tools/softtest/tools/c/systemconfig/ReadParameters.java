package softtest.tools.c.systemconfig;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.util.LinkedList;
import java.util.List;

public class ReadParameters {
	private final static String CONFIG_FILE = "config\\config.ini";
	private final static String NOTE_PREFIX = "#";
	public ReadParameters(){
		
	}
	public List<Parameters> initReadConfig(){
		List<Parameters> parameters = new LinkedList<Parameters>();
		File configFile = new File(CONFIG_FILE);
		if (configFile.exists()){
			try{
				BufferedReader reader = new BufferedReader(new FileReader(configFile));
				String config;
				while ((config = reader.readLine()) != null){
					if (config.startsWith(NOTE_PREFIX)){
						String description = config.substring(1).trim();
						if((config = reader.readLine()) != null){
							String[] configs = config.split(" ");
						    if(configs.length >= 2){
								String name = configs[0].substring(1).trim();
								StringBuffer value = new StringBuffer();
								for(int i=1;i<configs.length;i++){
						        	value.append(configs[i]);
						        }
								Parameters para = new Parameters(name,description,value);
								parameters.add(para);
						    }
						    if(configs.length == 1){
						    	String name ="";
						    	StringBuffer value = new StringBuffer();
						    	value.append(configs[0].substring(1).trim());
						    	Parameters para = new Parameters(name,description,value);
								parameters.add(para);
						    }
						}
					}
					
				}
			}
			catch (Exception e){
				System.err.println("Error in reading the config file.");
			}
		}
		return parameters;
	}	
}