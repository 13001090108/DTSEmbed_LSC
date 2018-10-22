package softtest.test.c.gcc;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

/**
 * 本类用于产生JUNIT参数化测试用例中的参数，即各文件的绝对路径。
 *  FileListFactory(String dirPath)执行后，将打印输出拷贝至目标文件中即可。
 * @author zys
 */
public class TestCaseGenerator
{
	private static final String filePathgcc="testcase/gcc/gcc.dg";
	private static final String filePathkeil="testcase/keilc";
	
	/**
	 * 1、通过外部工具搜索GCC下的源文件，如果其中出现dg-error，则表示本源文件编译错误，将
	 * 错误源文件列表保存为一个本地文件，命名为：testcase/gcc/errorfiles.txt；
	 * 2、在生成测试用例时，首先从上述errorfiles.txt中生成错误源文件列表；
	 * 3、在扫描相应目录时，将扫描到的源文件与列表中文件对比，如果出现则表示此文件编译错误，
	 * 不生成测试用例
	 */
	private static final String errorFilePath="testcase/gcc/errorfiles.txt";
	public static void main(String[] args)
	{
		ReadErrorSrcFiles(errorFilePath);
		FileListFactory(filePathgcc);
	}

	/**
	 * <p>
	 * 用于生成JUNIT参数化测试用例中的测试数据，即各待测试文件的绝对地址
	 * </p>
	 * @param dirPath
	 * 		目标文件夹的路径地址
	 * @return 
	 * 		打印生成的文件地址列表
	 */
	static StringBuilder sb=new StringBuilder();
	static int i=0;
	public static String FileListFactory(String dirPath)
	{
		File dir=new File(dirPath);
		if(!dir.isDirectory())
		{
			return dir.getAbsolutePath();
		}
		
		File[] fileList=dir.listFiles();
		int fileNum=fileList.length;
		for(int j=0;j<fileNum;j++)
		{
			if(fileList[j].isDirectory())
			{
				//FileListFactory(fileList[j].getAbsolutePath());
			}else {
				String filePath=fileList[j].getAbsolutePath();
				if(errorFiles.contains(filePath))
				{
					continue;
				}
				filePath=filePath.replace("\\","/");
				if(filePath.endsWith(".c") || filePath.endsWith(".C"))
				{
					/*sb.append("public void testSrcFile"+i+"() throws Exception\n{\n");
					sb.append("\tassert(new File(\"").append(filePath).append("\").exists());\n").append(
								"\tassertTrue(\"Parsed Failed\", setUp(\"").append(filePath).append("\"));\n}\n");
					System.out.println(sb.toString());*/
					sb.append("\n///////////////////  "+(i)+"   ///////////////////\n");
					sb.append("{\n\t\""+filePath+"\"\n"+"\t,"+"\n"+"\t\"OK\""+"\n},");
					System.out.print(sb.toString());
					i++;
				}
			}
			sb.delete(0, sb.length());
		}
		return sb.toString();
	}

	private static List<String> errorFiles = new ArrayList<String>();
	public static void ReadErrorSrcFiles(String errorFilePath)
	{
		File errorFile=new File(errorFilePath);
		if(!errorFile.exists())
			return;
		try
		{
			BufferedReader br=new BufferedReader(new FileReader(errorFile));
			String path;
			while((path=br.readLine())!=null)
			{
				int i=path.lastIndexOf(".c");
				path=path.substring(0, i+2);
				errorFiles.add(path);
			}
		} catch (FileNotFoundException e)
		{
			e.printStackTrace();
		} catch (IOException e1)
		{
			e1.printStackTrace();
		}
		
	}
}
