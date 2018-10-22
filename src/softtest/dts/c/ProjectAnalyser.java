package softtest.dts.c;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
/**
 * @author ssj
 */
public class ProjectAnalyser {
	public static final String PROJECTFILE_EXT = ".+\\.(Uv2|UV2|uv2|uV2|Uvproj|UVPROJ|uvproj|UVproj)$";
	public static final String U4_PROJFILE_POSTFIX = ".+\\.(uvproj|Uvproj|UVPROJ|UVproj)$";
    public static final String U3_PROJFILE_POSTFIX = ".+\\.(Uv2|UV2|uv2|uV2)$";
    public static final String SFILE_POSTFIX = ".+\\.(c|C)$";
    public static final String IFILE_POSTFIX = ".+\\.(h|H)(\"|>).*";
    public static final String PRE_POSTFIX = ".+\\.(i|I)$";
    
    private String fileName;
	
	public List<String> filePathList;
	
	public List<String> incDirs;
	
	public ProjectAnalyser(String fileName) {
		this.fileName = fileName;
		filePathList = new ArrayList<String>(); 
		incDirs = new ArrayList<String>();
	}
	public void process() throws ProjAnalyserException{
		String filePath = ".\\";
		if (fileName.lastIndexOf(File.separatorChar) != -1) {
			filePath = fileName.substring(0, fileName.lastIndexOf(File.separatorChar));
		}
		try{
			BufferedReader reader = new BufferedReader(new FileReader(fileName));
			String line = null;
			//收集KEIL U3版本下的相应工程的.C文件
			if (fileName.matches(U3_PROJFILE_POSTFIX)) {
				while((line = reader.readLine()) != null) {
					if (line.startsWith("File")) {
						String[] params = line.split(",");
						String sline = params[2];
						String[] paramss = sline.split(">");
						sline = paramss[1].trim().substring(1);
						if(sline.matches(SFILE_POSTFIX)){
							filePathList.add(filePath + File.separator + sline);
						}
					}
				}
			//收集KEIL U4版本下的相应工程的.C文件
			}else if (fileName.matches(U4_PROJFILE_POSTFIX)) {
				LinkedHashSet<String> cFile = new LinkedHashSet<String>();
				while((line = reader.readLine()) != null) {
					if(line.trim().startsWith("<FileName>")){
						String[] params = line.split(">");
						String sline = params[1];
						String[] paramss = sline.split("<");
						sline = paramss[0].trim();
						if(sline.matches(SFILE_POSTFIX)){
							cFile.add(filePath + File.separator + sline);
							//filePathList.add(filePath + File.separator + sline);
						}
					}
				}
				filePathList.addAll(cFile);
			}
			//.H文件处理
			/*LinkedHashSet<String> hFile = new LinkedHashSet<String>();
			for(int i = 0; i < filePathList.size(); i++){
				reader = new BufferedReader(new FileReader(filePathList.get(i)));
				while((line = reader.readLine()) != null) {
					if(line.startsWith("#include")){						
						if(line.matches(IFILE_POSTFIX)){
							//String[] params = line.split("\"");
							//String sline = params[1].trim();
							hFile.add(filePath);
							//hFile.add(filePath + File.separator + sline);
						}
					}
				}
			}	
			incDirs.addAll(hFile);*/
			incDirs.add(filePath);
		}catch (Exception e) {
			throw new ProjAnalyserException(e, "Error in reading the project file " + fileName);
		}
	}
}
