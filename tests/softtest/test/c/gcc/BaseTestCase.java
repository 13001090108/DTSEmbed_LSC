package softtest.test.c.gcc;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;

import softtest.ast.c.CCharStream;
import softtest.ast.c.CParser;
import softtest.ast.c.ParseException;
import softtest.pretreatment.PlatformType;
import softtest.pretreatment.Pretreatment;

/**
 * 本类作为gcc_test与keil_test回归测试的父类
 * @author zys赵云山	2009.12.17
 *
 */
public class BaseTestCase extends TestCase
{
	/**
	 * <p>Indicates which C language standard using in the test.</p>
	 */
	private static Pretreatment pre = new Pretreatment();
	
	private static ArrayList<String> includeFiles=new ArrayList<String>();//头文件列表
	
	private List<String> macroList = new ArrayList<String>();//宏定义列表
	
	/**
	 * 设置所用的编译器：gcc KEIL
	 * @param platform
	 */
	public static void setPlatformType(PlatformType platform)
	{
		pre.setPlatform(platform);
	}

	/**
	 * 导入头文件，初始化includeFiles
	 * @param includeDir
	 * 		头文件所在目录的地址
	 */
	public static void InitIncludeFiles(String includeDir)
	{
		File dir=new File(includeDir);
		if(!dir.exists())
			return;
		includeFiles.add(includeDir);//先将当前目录加入头文件目录
		File[] fileList=dir.listFiles();
		int length=fileList.length;
		for(int i=0;i<length;i++)
		{
			if(fileList[i].isDirectory())
				includeFiles.add(fileList[i].getAbsolutePath());
		}
	}
	
	/**
	 * 具体的测试方法类：先调用Pretreatment类对待测试文件进行预处理，将.c文件处理为.i文件，然后
	 * 调用CParser进行分析
	 * @param caseFileName
	 * 		待分析文件的路径，可以是文件或目录
	 * @return
	 * 		true,表示本文件分析成功；
	 * 		false,表示分析失败或出现异常
	 */
	public boolean test(String caseFileName)
	{
		File caseFile = new File(caseFileName);//待分析的C源文件或源文件夹
		List<String> interFileName = new ArrayList<String>();//预处理后的文件列表
		
		if(!caseFile.exists())
			return false;
		if (caseFile.isFile())
		{
			String interFilePath = pre.pretreat(caseFile.getAbsolutePath(),
					includeFiles, macroList);
			interFileName.add(interFilePath);
		}
		if (caseFile.isDirectory())
		{
			pre.batchPretreat(caseFile.getAbsolutePath(),interFileName);
		}

		CParser parser;
		java.io.InputStream input;
		for(String srcFile:interFileName)
		{
			try
			{
				input = new java.io.FileInputStream(new java.io.File(srcFile));
				CCharStream cs = new CCharStream(input);
				parser = CParser.getParser(cs);

				parser.TranslationUnit();
			} catch (java.io.FileNotFoundException e)
			{
				System.out.println("File  not found:"+srcFile);
				return false;
			} catch (ParseException e)
			{
				e.printStackTrace();
				System.out.println("\nEncountered errors during parse.In File:"+srcFile);
				return false;
			} 
		}
		return true;
	}

	private static String CONFIG_FILE = "config/config.ini";//用户配置文件：用于设定所用的编译器为GCC或KEIL
	private final static String NOTE_PREFIX = "#";//用户可以在其中配置所需的头文件
	/**
	 * 		从CONFIG_FILE中读取用户设置的编译器类型
	 * @return
	 * 		返回值为keil 或 gcc
	 */
	public static String initFileType()
	{
		File configFile = new File(CONFIG_FILE);
		if (configFile.exists())
		{
			try
			{
				BufferedReader reader = new BufferedReader(new FileReader(
						configFile));
				String config;
				while ((config = reader.readLine()) != null)
				{
					if (config.trim().startsWith(NOTE_PREFIX) 
							|| config.trim().startsWith("-D"))
					{
						continue;
					}else if(config.trim().startsWith("-I"))
					{
						//GCC所需的外部自定义头文件（非系统头文件）
						//includeFiles.add(o);//从config.ini文件中读取外部定义的头文件
						continue;
					}else if (config.trim().equalsIgnoreCase("-gcc"))
					{
						CParser.setType("gcc");
						return "gcc";
					} else if (config.trim().equalsIgnoreCase("-keil"))
					{
						CParser.setType("keil");
						return "keil";
					}
				}
			} catch (Exception e)
			{
				System.err.println("Error in reading the config file.");
				e.printStackTrace();
				return null;
			}
		}
		return null;
	}
}
