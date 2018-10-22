package softtest.fsmanalysis.c;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

public class UnknownString
{

	private static String userDir = System.getProperty("user.dir");
	private static String REPLACE_FILE = userDir + "\\cpp\\replace.txt";
	private static Object[] define;
	private static Object[] replaceBy;
	
	public static void  setReplaceString(){
		List<String> listDefine = new ArrayList<String>();
		List<String> listreplaceBy = new ArrayList<String>();
		File replace = new File(REPLACE_FILE);
		BufferedReader read = null;
		try {
			read = new BufferedReader(new FileReader(replace));
			String line = null;
			String[] temp;
			int i=1;
			while((line = read.readLine()) != null) {
				temp = line.split("##");
				if(temp.length>2||temp.length<1)
					continue;
				listDefine.add(" "+temp[0].trim()+" ");
				if(temp.length==1 || temp[1]==null || temp[1].trim().equals(""))
					listreplaceBy.add(" ");
				else 
					listreplaceBy.add(" "+temp[1].trim()+" ");
				i++;
			}
		} catch (Exception e) {
			throw new RuntimeException("Error in reading file :" + replace.getAbsolutePath());
		}
		//added finally by liuyan 2015.6.3
		finally{
			if( read != null ){
				try {
					read.close();
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
		}
		define = listDefine.toArray();
		replaceBy = listreplaceBy.toArray();
	}
	public static Object[] getdefine(){
		return define;
	}
	public static Object[] getreplaceBy(){
		return replaceBy;
	}
}
