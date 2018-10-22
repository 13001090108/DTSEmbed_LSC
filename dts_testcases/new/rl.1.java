//ZipFile资源识别

import java.io.File;                                                 
import java.io.IOException;                                          
import java.util.zip.ZipException;                                   
import java.util.zip.ZipFile;                                        
public class test {                                                  
	void process(File zipFile) throws ZipException, IOException {       
		ZipFile contents = new ZipFile(zipFile);                           
		return;                                                            
	}                                                                   
}
