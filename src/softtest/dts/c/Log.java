package softtest.dts.c;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.Properties;

import org.apache.log4j.Logger;
import org.apache.log4j.PropertyConfigurator;

import softtest.config.c.Config;

public class Log { 
	static Logger logger = Logger.getLogger(Log.class); 
	
	public Log() 
	{ } 
	
	public static void init(String projectName){ 
//		Config.LOG_FILE=".\\log\\";
		Config.FILE = Config.LOG_FILE+projectName+".log";
		String logFileNameINFO = Config.LOG_FILE+projectName+".log";//info
		String logFileNameERROR = Config.LOG_FILE+projectName+"_error"+".log";//error
		Properties props = new Properties(); 
		FileInputStream istream = null;
		FileOutputStream outstream = null;
		try { 
			File directory = new File("");
			String proFilePath = directory.getCanonicalPath() ; 
			File log4jFile=new File(proFilePath,"log4j.properties");
			istream = new FileInputStream(log4jFile); 
			props.load(istream); 
			/*istream.close(); */
			//info日志
			props.setProperty("log4j.appender.info.File",logFileNameINFO); 
			if( Config.LOG_REPLACE == true){
				props.setProperty("log4j.appender.info.Append", "false");
			}else{
				props.setProperty("log4j.appender.info.Append", "true");
			}
			//error日志
			props.setProperty("log4j.appender.error.File",logFileNameERROR); 
			if( Config.LOG_REPLACE == true){
				props.setProperty("log4j.appender.error.Append", "false");
			}else{
				props.setProperty("log4j.appender.error.Append", "true");
			}
			outstream = new FileOutputStream(log4jFile); 
			props.save(outstream, "");
//			outstream.close();
			PropertyConfigurator.configure(props); 
		} catch (IOException e) { 
				return; 
		} 
		//added finally by liuyan 2015.6.5
		finally{
			if(istream != null){
				try {
					istream.close();
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				} 
			}
			if(outstream != null){
				try {
					outstream.close();
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
		}
	} 
	
	public static void error(Object message)
	{
		if(Config.PRINT_LOG_ERROR)
		{
			logger.error(message);
		}
	}
	
	public static void error(Object message,Throwable t)
	{
		if(Config.PRINT_LOG_ERROR)
		{
			logger.error(message, t);
		}
	}
	
	
} 


