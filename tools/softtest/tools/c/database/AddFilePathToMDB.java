package softtest.tools.c.database;

import java.io.File;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.HashMap;

/**如果是-I分析方式，由于中间文件是由第三方生成，其中的源文件路径信息可能丢失（IP数据库中只有文件名，或者缺失文件路径），
 * 导致IP确认时需要人工进行替换。本工具的功能：
 * <p>输入IP数据库，及数据库对应的工程目录，可以自动补全缺失的路径信息，方便IP确认</p> 
 * <p>目前的缺陷：对于文件名重复的情况，无法处理。。。</p>
 * 
 * 2010.12.18
 * */
public class AddFilePathToMDB {

	/**暂存从数据库中读取的文件名,存在文件路径的不处理，同名文件暂时不考虑 */
	private ArrayList<String> dbFileNameList=null;
	
	//暂存源文件夹下的所有.c文件
	HashMap<String,String> srcFileList=null;
	
	private String path_MDB="";
	
	private Connection conn=null;
	
	public static final char FILE_SEPARATOR=File.separatorChar;
	
	public AddFilePathToMDB(String mdbPath)
	{
		this.path_MDB=mdbPath;
		dbFileNameList=new ArrayList<String>();
		srcFileList=new HashMap<String,String>();
		openDatabase(path_MDB);
	}
	
	public static void main(String[] args) {
		/* 
		 * "E:\\DTSGCC\\Mdb\\symbolic\\antiword_interfile.mdb";
		 * "E:\\DTSGCC\\TestCase\\antiword-0.37\\antiword-0.37";
		 * 
		 * 
		 * "E:\\DTSGCC\\TestCase\\make-3.81\\make-3.81";
		 * 
		 * String mdbPath="E:\\DTSGCC\\Mdb\\binutils4.mdb";
		String srcDir="E:\\DTSGCC\\TestCase\\binutils-2.20.1\\src";
		 */
		if(args.length!=2){
			System.out.println("参数输入不正确！\nparam1: the mdb to be replaced" +
					"\nparam2: the source file absolute path");
			return;
		}
		String mdbPath=args[0];
		String srcDir=args[1];
		AddFilePathToMDB t=new AddFilePathToMDB(mdbPath);
		t.queryFileNameFromMDB();
		//System.out.println(t.getFileNameList().size());
		t.queryAllSrcFiles(srcDir);
		//System.out.println(t.getSrcFileList().size());
		int i=t.updateFilePathInMDB();
		System.out.println(i);
	}

	private void openDatabase(String mdbPath){
		File file = new File(mdbPath);
		if (!file.exists()) {
			throw new RuntimeException("目标数据库不存在！");
		}
		
		String driver = "sun.jdbc.odbc.JdbcOdbcDriver";
		String url = "jdbc:odbc:DRIVER=Microsoft Access Driver (*.mdb);DBQ=" + mdbPath;
		try {
			Class.forName(driver);
			conn = DriverManager.getConnection(url, "", "");
		} catch (ClassNotFoundException ex) {
			throw new RuntimeException("Access database driver error",ex);
		} catch (SQLException ex) {
			throw new RuntimeException("Access database connect error",ex);
		}
	}
	
	private void queryFileNameFromMDB()
	{
		String sql="select distinct File from IP";
		ResultSet rs=null;
		Statement stmt=null;
		try {
			stmt = conn.createStatement();
			rs=stmt.executeQuery(sql);
			String name="";
			while (rs.next()) {
				name=rs.getString(1);
				dbFileNameList.add(name);
			}
		} catch (SQLException e) {
			e.printStackTrace();
		} finally{
			try {
				rs.close();
				stmt.close();
			} catch (SQLException e) {
				e.printStackTrace();
			}
		}
	}
	
	/**从源文件夹中查询所有的.c文件，重名文件不重复添加 */
	private void queryAllSrcFiles(String dirPath){
		File srcDir=new File(dirPath);
		if(!srcDir.exists()){
			throw new RuntimeException("源文件夹不存在！");
		}
		File[] fileList=srcDir.listFiles();
		int fileNum=fileList.length;
		for(int j=0;j<fileNum;j++){
			if(fileList[j].isDirectory())
			{
				queryAllSrcFiles(fileList[j].getAbsolutePath());
			}else {
				String filePath=fileList[j].getAbsolutePath();
				filePath=filePath.replace("\\","/");
				if(filePath.endsWith(".c") || filePath.endsWith(".C")
						|| filePath.endsWith(".def") || filePath.endsWith(".y"))
				{//部分源文件的后缀为def
					String fileName=fileList[j].getName();
					if(srcFileList.get(fileName)!=null){
						srcFileList.remove(fileName);
						System.out.println("源文件中存在同名文件"+fileName+"，请手动替换！");
					}else{
						srcFileList.put(fileName, filePath);
					}
				}
			}
		}
	}
	
	private int updateFilePathInMDB(){
		int updateCount=0;
		String sql="";
		String path="";
		Statement stmt=null;
		try {
			stmt=conn.createStatement();
			for(String file : dbFileNameList){
				String name=file;
				if(name.indexOf(':')>=0){
					//如果出现windows中的盘符，则说明存在完整路径
					continue;
				}
				else if(name.indexOf(FILE_SEPARATOR)>=0){
					//如果出现相对路径，则查找文件名
					int i=name.lastIndexOf(FILE_SEPARATOR);
					name=name.substring(i+1, name.length());
				}
				
				path=srcFileList.get(name);
				if(path!=null){
					sql="update IP set File="+"\'"+path+"\'"+" where File="+"\'"+file+"\'";
					updateCount+=stmt.executeUpdate(sql);
				}else{
					System.out.println("未查找到源文件路径："+name);
				}
			}
		} catch (SQLException e) {
			e.printStackTrace();
		} finally{
			try {
				stmt.close();
				conn.close();
			} catch (SQLException e) {
				e.printStackTrace();
			}
		}
		return updateCount;
	}

	public ArrayList<String> getFileNameList() {
		return dbFileNameList;
	}

	public void setFileNameList(ArrayList<String> fileNameList) {
		this.dbFileNameList = fileNameList;
	}

	public HashMap<String, String> getSrcFileList() {
		return srcFileList;
	}

	public void setSrcFileList(HashMap<String, String> srcFileList) {
		this.srcFileList = srcFileList;
	}
}
