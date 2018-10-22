package softtest.database.c;

import java.sql.*;
import java.io.*;
import java.util.*;
import java.util.Date;

import softtest.cluster.c.SimpleBean;
import softtest.config.c.Config;
import softtest.dscvp.c.DSCVPElement;
import softtest.dts.c.DTSC;
import softtest.fsmanalysis.c.ProjectStat;
import softtest.interpro.c.InterContext;

public class DBAccess {

	public static String TEMPLATE_MDB_PATH = "..\\set\\Dbtemplate.Mdb";
	public static String STAT_TEMPLATE_MDB_PATH = "..\\set\\stattemplate.Mdb";
	public static String CONFIG_MDB_PATH = "..\\set\\config.mdb";
	public static String STAT_MDB_PATH = "stat\\stat.mdb";

	/** 数据库连接 */
	private Connection dbcon;
	private Connection statcon;
	
	/**xwt 用于输出非缺陷模式数据库*/
	private Connection _dbcon;

	private static int errNum=0;
	private static int complementNum = 0;
	private int IP_ID = 0;

	public int getErrNum(){
		return errNum;
	}
	public int getComplementNum(){
		return complementNum;
	}

	private static DBAccess instance;

	private DBAccess() {
	}

	public static DBAccess getInstance() {
		if (instance == null) {
			instance = new DBAccess();
		}
		return instance;
	}


	/** 文件拷贝 */
	public static void copyFileToFile(String F1, String F2) {
		// 现文件对拷,从F1拷贝到F2,若F2存在则会被覆盖;适用于任何文件.
		FileInputStream fis = null;
		FileOutputStream fos = null;
		try {
			fis = new FileInputStream(F1); // 建立文件输入流
			fos = new FileOutputStream(F2);
			byte[] buffer = new byte[1024];
			int len;
			while ((len = fis.read(buffer)) != -1) {
				fos.write(buffer, 0, len);
			}
		} catch (FileNotFoundException ex) {
			// ex.printStackTrace();
			throw new RuntimeException("连接数据库文件 " + F1 + "出错", ex);
		} catch (IOException ex) {
			// ex.printStackTrace();
			throw new RuntimeException("连接数据库文件 " + F1 + "出错",ex);
		} finally {
			try {
				if (fis != null)
					fis.close();
				if (fos != null)
					fos.close();
			} catch (IOException ex) {
				// ex.printStackTrace();
				throw new RuntimeException("连接数据库文件 Dbtemplate.mdb出错",ex);
			}
		}
	}

	/** 清空mdb文件的数据 */
	private static void clearData(String pathname) {
		String driver = "sun.jdbc.odbc.JdbcOdbcDriver";
		String url = "jdbc:odbc:DRIVER=Microsoft Access Driver (*.mdb);DBQ="
				+ pathname;
		Connection conn = null;
		Statement stmt = null;

		try {
			Class.forName(driver);
			conn = DriverManager.getConnection(url, "", "");
			stmt = conn.createStatement();
			String sql = "delete * from IP";
			stmt.executeUpdate(sql);
		} catch (ClassNotFoundException ex) {
			// ex.printStackTrace();
			throw new RuntimeException("Access database driver error",ex);
		} catch (SQLException ex) {
			// ex.printStackTrace();
			throw new RuntimeException("Access database connect error1",ex);
		} finally {
			if (stmt != null) {
				try {
					stmt.close();
				} catch (SQLException ex) {
					// ex.printStackTrace();
					throw new RuntimeException("Access database connect error2",ex);
				}
			}
			if (conn != null) {
				try {
					conn.close();
				} catch (SQLException ex) {
					// ex.printStackTrace();
					throw new RuntimeException("Access database connect error3",ex);
				}
			}
		}
	}

	/** 创建一个新的空的mdb文件 */
	public static void createMdbFile(String templateName, String pathname) {
		copyFileToFile(templateName, pathname);
		//clearData(pathname);
	}

	/** 读取指定行的DSCVPyang add 20161109 */
	public Hashtable<Integer, String> readDSCVP(){
		Hashtable<Integer, String> res = new Hashtable<Integer, String>();
		PreparedStatement select = null;
		try {
			String strSQL="SELECT num,dscvp FROM IP";
			select = dbcon.prepareStatement(strSQL);
			ResultSet result = select.executeQuery();
			// 产生一个新的唯一编号
			while (result.next()) {
				int key = result.getInt(1);
				//String s = result.getString(1);
				String value = result.getString(2);
				if (key > 0){
					res.put(key, value);
				}
			}

		} catch (SQLException e) {
			e.printStackTrace();
			throw new RuntimeException("Access database connect error8",e);
		}
		finally {
			if (select != null) {
				try { select.close(); } catch (Exception e) {}
			}
		}
		return res;
	}
	
	
	/** 指定行写入DSCVP*/
	public void writeDSCVP(int num, String dscvp){
		PreparedStatement pstmt = null;
		if (dbcon == null) {
			throw new RuntimeException("database connection closed.");
		}
		try {
			String strSQL="UPDATE IP SET DSCVP=? WHERE Num=?";
			pstmt = dbcon.prepareStatement(strSQL);
			// 设置插入的值
			pstmt.setString(1, dscvp);
			pstmt.setInt(2, num);
			pstmt.executeUpdate();
			
		} catch (SQLException e) {
			e.printStackTrace();
			throw new RuntimeException("Access database connect error8",e);
		}
		finally {
			if (pstmt != null) {
				try {
					pstmt.close();
				} catch (SQLException ex) {
					// ex.printStackTrace();
					throw new RuntimeException("Access database connect error16",ex);
				}
			}
		}
	}
	
	/** 读取数据库到simplebeanList中,add by JJL, 20161204*/
	public List<SimpleBean> readAccess(){
		List<SimpleBean> res = new ArrayList<SimpleBean>();
		PreparedStatement select = null;
		try {
			String strSQL="SELECT * FROM IP";
			select = dbcon.prepareStatement(strSQL);
			ResultSet rset = select.executeQuery();
			// 产生一个新的唯一编号
			while (rset.next()) {
				String Num = rset.getString("Num");
				String Fault = rset.getString("Defect");
				String Category = rset.getString("Category");
				String Variable = rset.getString("Variable");
				String File = rset.getString("File");
				String Method = rset.getString("Method");
				String StartLine = rset.getString("StartLine");
				String IPLine = rset.getString("IPLine");
				String stringF = rset.getString("DSCVP");
				String Equal = rset.getString("Equal");
				String Related = rset.getString("Related");

				DSCVPElement eroot = getDipByString(Num, Variable, stringF, File, Method, IPLine);
				SimpleBean sb = new SimpleBean(Num, Fault, Category, Variable, stringF, eroot, Equal, Related, File, Method, StartLine, IPLine);
				res.add(sb);
			}

		} catch (SQLException e) {
			e.printStackTrace();
			throw new RuntimeException("Access database connect error8",e);
		}
		finally {
			if (select != null) {
				try { select.close(); } catch (Exception e) {}
			}
		}
		return res;
	}
	
	/**将dblist写入数据库中更新DSCVP字段,add by JJL,20161204*/
	public void writeAccessToDSCVP(List<SimpleBean> dbList) {
		for (int j = 0; j < dbList.size(); j++) {
			SimpleBean listSB = dbList.get(j);
			
			PreparedStatement pstmt = null;
			if (dbcon == null) {
				throw new RuntimeException("database connection closed.");
			}
			try {
				String strSQL="UPDATE IP SET DSCVP=? WHERE Num=?";
				pstmt = dbcon.prepareStatement(strSQL);
				// 设置插入的值
				pstmt.setString(1, listSB.getStringF());
				pstmt.setInt(2, Integer.valueOf( listSB.getNum()));
				pstmt.executeUpdate();
				
			} catch (SQLException e) {
				e.printStackTrace();
				throw new RuntimeException("Access database connect error8",e);
			}
			finally {
				if (pstmt != null) {
					try {
						pstmt.close();
					} catch (SQLException ex) {
						// ex.printStackTrace();
						throw new RuntimeException("Access database connect error16",ex);
					}
				}
			}
			
		}
	}
	
	/**将dblist写入数据库中更新equal,similar字段,add by JJL,20161204*/
	public void writeAccessToCluster(List<SimpleBean> dbList) {
		for (int j = 0; j < dbList.size(); j++) {
			SimpleBean listSB = dbList.get(j);
			
			PreparedStatement pstmt = null;
			if (dbcon == null) {
				throw new RuntimeException("database connection closed.");
			}
			try {
				String strSQL="UPDATE IP SET Equal = ?, Related = ? WHERE Num=?";
				pstmt = dbcon.prepareStatement(strSQL);
				// 设置插入的值
				pstmt.setString(1, listSB.getEqual());
				pstmt.setString(2, listSB.getRelated());
				pstmt.setInt(3, Integer.valueOf( listSB.getNum()));
				pstmt.executeUpdate();
				
			} catch (SQLException e) {
				e.printStackTrace();
				throw new RuntimeException("Access database connect error8",e);
			}
			finally {
				if (pstmt != null) {
					try {
						pstmt.close();
					} catch (SQLException ex) {
						// ex.printStackTrace();
						throw new RuntimeException("Access database connect error16",ex);
					}
				}
			}
			
		}
	}
	
	/** 根据数据库中DSCVP字段找到相对应的DSCVPElement ，add by JJL,20161204*/
	private DSCVPElement getDipByString(String num, String variable,
			String F, String file, String method, String iPLine) {
		DSCVPElement eroot = null;
		DTSC dtsc = new DTSC();
		HashMap<String, DSCVPElement> map = dtsc.getDipList();
		if (map.containsKey(F)) {
			eroot = map.get(F);
		}
		if (eroot != null) {
			System.out.println(num +"-find");
		} else {
			System.out.println(num + "-none");
		}
		return eroot;
	}
	
	/** 读取扫描设置 */
	public static Map<String, String> getScanTypes(String pathname) {
		Map<String, String> fsms = new HashMap<String, String>();
		//debug
		//pathname = "C:\\Users\\Administrator\\workspace\\DTSEmbed\\set\\config.mdb";
		String driver = "sun.jdbc.odbc.JdbcOdbcDriver";
		String url = "jdbc:odbc:DRIVER=Microsoft Access Driver (*.mdb);DBQ="
				+ pathname;
		Connection conn = null;
		Statement stmt = null;
		try {
			Class.forName(driver);
			conn = DriverManager.getConnection(url, "", "");
			stmt = conn.createStatement();
			String sql = "";
			//sql = "select * from 扫描配置";
			sql = "select * from ScanSet";
			ResultSet rs = stmt.executeQuery(sql);
			
			while (rs.next()) {
				if (rs.getBoolean(5)) {
					fsms.put(rs.getString(3), rs.getString(2));
				}
			}
		} catch (ClassNotFoundException ex) {
			// ex.printStackTrace();
			throw new RuntimeException("连接数据库文件 config.mdb出错",ex);
		} catch (SQLException ex) {
			// ex.printStackTrace();
			throw new RuntimeException("连接数据库文件 config.mdb出错",ex);
		} finally {
			if (stmt != null) {
				try {
					stmt.close();
				} catch (SQLException ex) {
					// ex.printStackTrace();
					throw new RuntimeException("连接数据库文件 config.mdb出错",ex);
				}
			}
			if (conn != null) {
				try {
					conn.close();
				} catch (SQLException ex) {
					// ex.printStackTrace();
					throw new RuntimeException("连接数据库文件 config.mdb出错",ex);
				}
			}
		}
		return fsms;
	}

	public void openDataBase(String dbName) {
		if (dbcon == null) {
			dbcon = openDataBase(dbName, TEMPLATE_MDB_PATH);
			IP_ID = getMaxIpId();
		}
	}
	
	/**xwt 2011.11.3 打开非缺陷模式数据库*/
	public void openComplementDB(String dbName) {
		if (_dbcon == null) {
			_dbcon = openDataBase(dbName, TEMPLATE_MDB_PATH);
			IP_ID = getMaxIpId();
		}
	}

	/** 打开数据库连接 */
	public Connection openDataBase(String dbName, String templateName) {
		Connection conn;
		File file = new File(dbName);
		if (!file.exists()) {
			DBAccess.createMdbFile(templateName, dbName);
		}
		String driver = "sun.jdbc.odbc.JdbcOdbcDriver";
		String url = "jdbc:odbc:DRIVER=Microsoft Access Driver (*.mdb);PWD=" + getPassword() + ";DBQ="+ dbName;
		try {
			Class.forName(driver);
			conn = DriverManager.getConnection(url, "", "");
		} catch (ClassNotFoundException ex) {
			// ex.printStackTrace();
			throw new RuntimeException("Access database driver error",ex);
		} catch (SQLException ex) {
			 ex.printStackTrace();
			throw new RuntimeException("Access database connect error4");
		}
		return conn;
	}

	/** 关闭数据库连接 */
	public void closeDataBase() {
		if (dbcon != null) {
			try {
				dbcon.close();
			} catch (SQLException ex) {
				// ex.printStackTrace();
				throw new RuntimeException("Access database connect error6",ex);
			}
		}
		dbcon = null;
	}
	
	public void closeComplementDB() {
		if (_dbcon != null) {
			try {
				_dbcon.close();
			} catch (SQLException ex) {
				// ex.printStackTrace();
				throw new RuntimeException("Access database connect error6",ex);
			}
		}
		_dbcon = null;
	}

	private Map getIpCountByCategory() {
		PreparedStatement select = null;
		Map stat = new HashMap();
		try {
			String strSQL="SELECT defect,category FROM IP WHERE Num > ?";
			select = dbcon.prepareStatement(strSQL);
			select.setInt(1, IP_ID);
			ResultSet result = select.executeQuery();

			while (result.next()) {
				String defect = result.getString(1);
				String category = result.getString(2);
				String key = defect.concat(" ").concat(category);
				if (stat.containsKey(key)) {
					int num = (Integer) stat.get(key);
					stat.put(key, num+1);
				} else {
					stat.put(key, 1);
				}
			}
		} catch (SQLException e) {
			e.printStackTrace();
			throw new RuntimeException("Access database connect error7",e);
		}
		finally {
			if (select != null) {
				try { select.close(); } catch (Exception e) {}
			}
		}
		return stat;
	}

	private int getMaxIpId() {
		int key = 0;
		Statement select = null;
		try {
			String strSQL="SELECT max(Num) FROM IP";
			select = dbcon.createStatement();
			ResultSet result = select.executeQuery(strSQL);
			// 产生一个新的唯一编号
			if (result.next()) {
				String str = result.getString(1);
				if (str != null) {
					key = Integer.parseInt(str);
				}
			}

		} catch (SQLException e) {
			e.printStackTrace();
			throw new RuntimeException("Access database connect error8",e);
		}
		finally {
			if (select != null) {
				try { select.close(); } catch (Exception e) {}
			}
		}
		return key;
	}

	private int getMaxScanId() {
		int key = 0;
		Statement select = null;
		try {
			String strSQL="SELECT MAX(id) FROM total";
			select = statcon.createStatement();
			ResultSet result = select.executeQuery(strSQL);
			// 产生一个新的唯一编号
			if (result.next()) {
				String str = result.getString(1);
				if (str != null) {
					key = Integer.parseInt(str);
				}
			}

		} catch (SQLException e) {
			e.printStackTrace();
			throw new RuntimeException("Access database connect error9",e);
		}
		finally {
			if (select != null) {
				try { select.close(); } catch (Exception e) {}
			}
		}
		return key;
	}

	/**
	 * 输出统计信息
	 * 增加一个统计功能,每次扫描完成后,将下列结果自动统计到一个数据库或者表中.
	 * 包括: 项目名、程序语言、文件个数、代码行、ip总数或每种缺陷ip数、测试时间、
	 * 扫描过程时间、确认故障数(保留字段,供用户填写)。
	 */
	private void exportStatisticsAll(String projectName,
			                            String date,
			                            long usedTime,
			                            long syntaxTreeTime,
										long symbolTableTime,
										long globalAnalysisTime,
			                            String language,
			                            String version,
			                            int fileCount,
			                            int timeOutFileCount,
			                            int lineCount,
			                            int ipCount,
			                            int ackIpCount) {
		PreparedStatement pstmt = null;
		if (statcon == null) {
			throw new RuntimeException("database connection closed.");
		}
		try {
			// 预编译指令
			String strSQL="insert into total (project,scandate,usedtime,syntaxTreeTime,symbolTableTime,globalAnalysisTime,language,dtsversion,filecount,timeoutfilecount,linecount,ipcount,ackipcount) values (?,?,?,?,?,?,?,?,?,?,?,?,?)";

			pstmt = statcon.prepareStatement(strSQL);
			// 设置插入的值
			pstmt.setString(1, projectName);
			pstmt.setString(2, date);
			pstmt.setInt(3, (int)usedTime);
			pstmt.setInt(4, (int)syntaxTreeTime);
			pstmt.setInt(5, (int)symbolTableTime);
			pstmt.setInt(6, (int)globalAnalysisTime);
			pstmt.setString(7, language);
			pstmt.setString(8, version);
			pstmt.setInt(9, fileCount);
			pstmt.setInt(10, timeOutFileCount);
			pstmt.setInt(11, lineCount);
			pstmt.setInt(12, ipCount);
			pstmt.setInt(13, ackIpCount);
			// 插入
			pstmt.executeUpdate();
		} catch (SQLException ex) {
			ex.printStackTrace();
			throw new RuntimeException("Access database connect error10",ex);
		} finally {
			if (pstmt != null) {
				try {
					pstmt.close();
				} catch (SQLException ex) {
					//ex.printStackTrace();
					throw new RuntimeException("Access database connect error11",ex);
				}
			}
		}
	}

	private void exportStatistics(String projectName,
										String date,
										long usedTime,
										String language,
										String version,
										int fileCount,
										int lineCount,
										String eclass,
										String ekind,
										int ipCount,
										int ackIpCount,
										int scanid) {
		PreparedStatement pstmt = null;
		if (statcon == null) {
			throw new RuntimeException("database connection closed.");
		}
		try {
			// 预编译指令
			String strSQL="insert into detail (project,scandate,usedtime,language,dtsversion,filecount,linecount,defect,category,cat_ipcount,cat_ackipcount,scanid) " +
					"values (?,?,?,?,?,?,?,?,?,?,?,?)";

			pstmt = statcon.prepareStatement(strSQL);
			// 设置插入的值
			pstmt.setString(1, projectName);
			pstmt.setString(2, date);
			pstmt.setInt(3, (int)usedTime);
			pstmt.setString(4, language);
			pstmt.setString(5, version);
			pstmt.setInt(6, fileCount);
			pstmt.setInt(7, lineCount);
			pstmt.setString(8, eclass);
			pstmt.setString(9, ekind);
			pstmt.setInt(10, ipCount);
			pstmt.setInt(11, ackIpCount);
			pstmt.setInt(12, scanid);
			// 插入
			pstmt.executeUpdate();
		} catch (SQLException ex) {
			ex.printStackTrace();
			throw new RuntimeException("Access database connect error12",ex);
		} finally {
			if (pstmt != null) {
				try {
					pstmt.close();
				} catch (SQLException ex) {
					//ex.printStackTrace();
					throw new RuntimeException("Access database connect error13",ex);
				}
			}
		}
	}

	/**
	 * 向数据库输出一条错误记录 参数含义：缺陷、类别、文件、变量名、起始行、错误行
	 */
	public void exportErrorData(String IPMethod,String eclass, String ekind, String pathname,
			String variable, int beginline, int errorline,String errorMessage,String code, String preconditions,String traceinfo,String dscvp) {
		Statement select = null;
		PreparedStatement pstmt = null;
		if (dbcon == null) {
			throw new RuntimeException("database connection closed.");
		}
		try {
			String strSQL="";
			// 预编译指令
			//strSQL="insert into IP (缺陷,类别,文件,变量名,起始行,错误行,错误描述,错误行代码) values (?,?,?,?,?,?,?,?,?)";
			strSQL="insert into IP (Defect,Category,File,Variable,StartLine,IPLine,Description,IPLineCode,PreConditions,TraceInfo,Method,DSCVP) values (?,?,?,?,?,?,?,?,?,?,?,?)";

			pstmt = dbcon.prepareStatement(strSQL);
			// 设置插入的值
			pstmt.setString(1, eclass);
			pstmt.setString(2, ekind);
			pstmt.setString(3, pathname);
			pstmt.setString(4, variable);
			pstmt.setInt(5, beginline);
			pstmt.setInt(6, errorline);
			pstmt.setString(7, errorMessage);
			pstmt.setString(8, code);
			pstmt.setString(9, preconditions);
			pstmt.setString(10, traceinfo);
			pstmt.setString(11, IPMethod);
			pstmt.setString(12, dscvp);
			// 插入
			pstmt.executeUpdate();
			errNum++;
		} catch (SQLException ex) {
			ex.printStackTrace();
			throw new RuntimeException("Access database connect error14",ex);
		}catch(Exception e)
		{
			
		}
		finally {
			if (select != null) {
				try {
					select.close();
				} catch (SQLException ex) {
					// ex.printStackTrace();
					throw new RuntimeException("Access database connect error15",ex);
				}
			}
			if (pstmt != null) {
				try {
					pstmt.close();
				} catch (SQLException ex) {
					// ex.printStackTrace();
					throw new RuntimeException("Access database connect error16",ex);
				}
			}
		}
	}
	
	/**
	 * 向数据库输出一条错误记录 参数含义：缺陷、类别、文件、变量名、起始行、错误行
	 */
	public void exportErrorData(String IPMethod,String eclass, String ekind, String pathname,
			String variable, int beginline, int errorline,String errorMessage,String code, String preconditions,String traceinfo) {
		Statement select = null;
		PreparedStatement pstmt = null;
		if (dbcon == null) {
			throw new RuntimeException("database connection closed.");
		}
		try {
			String strSQL="";
			// 预编译指令
			//strSQL="insert into IP (缺陷,类别,文件,变量名,起始行,错误行,错误描述,错误行代码) values (?,?,?,?,?,?,?,?,?)";
			strSQL="insert into IP (Defect,Category,File,Variable,StartLine,IPLine,Description,IPLineCode,PreConditions,TraceInfo,Method) values (?,?,?,?,?,?,?,?,?,?,?)";

			pstmt = dbcon.prepareStatement(strSQL);
			// 设置插入的值
			pstmt.setString(1, eclass);
			pstmt.setString(2, ekind);
			pstmt.setString(3, pathname);
			pstmt.setString(4, variable);
			pstmt.setInt(5, beginline);
			pstmt.setInt(6, errorline);
			pstmt.setString(7, errorMessage);
			pstmt.setString(8, code);
			pstmt.setString(9, preconditions);
			pstmt.setString(10, traceinfo);
			pstmt.setString(11, IPMethod);
			// 插入
			pstmt.executeUpdate();
			errNum++;
		} catch (SQLException ex) {
			ex.printStackTrace();
			throw new RuntimeException("Access database connect error14",ex);
		}catch(Exception e)
		{
			
		}
		finally {
			if (select != null) {
				try {
					select.close();
				} catch (SQLException ex) {
					// ex.printStackTrace();
					throw new RuntimeException("Access database connect error15",ex);
				}
			}
			if (pstmt != null) {
				try {
					pstmt.close();
				} catch (SQLException ex) {
					// ex.printStackTrace();
					throw new RuntimeException("Access database connect error16",ex);
				}
			}
		}
	}

	/**
	 * 向数据库输出一条非缺陷记录 参数含义：缺陷、类别、文件、变量名、起始行、错误行
	 */
	public void exportComplementData(String method,String eclass, String ekind, String pathname,
			String variable, int beginline, int errorline,String errorMessage,String code, String preconditions,String traceinfo) {
		Statement select = null;
		PreparedStatement pstmt = null;
		if (_dbcon == null) {
			throw new RuntimeException("database connection closed.");
		}
		try {
			String strSQL="";
			// 预编译指令
			//strSQL="insert into IP (缺陷,类别,文件,变量名,起始行,错误行,错误描述,错误行代码) values (?,?,?,?,?,?,?,?,?)";
			strSQL="insert into IP (Defect,Category,File,Variable,StartLine,IPLine,Description,IPLineCode,PreConditions,TraceInfo,Method) values (?,?,?,?,?,?,?,?,?,?,?)";

			pstmt = _dbcon.prepareStatement(strSQL);
			// 设置插入的值
			pstmt.setString(1, eclass);
			pstmt.setString(2, ekind);
			pstmt.setString(3, pathname);
			pstmt.setString(4, variable);
			pstmt.setInt(5, beginline);
			pstmt.setInt(6, errorline);
			pstmt.setString(7, errorMessage);
			pstmt.setString(8, code);
			pstmt.setString(9, preconditions);
			pstmt.setString(10, traceinfo);
			pstmt.setString(11, method);
			// 插入
			pstmt.executeUpdate();
			complementNum++;
		} catch (SQLException ex) {
			ex.printStackTrace();
			throw new RuntimeException("Access database connect error14",ex);
		} finally {
			if (select != null) {
				try {
					select.close();
				} catch (SQLException ex) {
					// ex.printStackTrace();
					throw new RuntimeException("Access database connect error15",ex);
				}
			}
			if (pstmt != null) {
				try {
					pstmt.close();
				} catch (SQLException ex) {
					// ex.printStackTrace();
					throw new RuntimeException("Access database connect error16",ex);
				}
			}
		}
	}
	
	/**
	 * 根据参数读取源码信息，文件路径，起始行号，起始列号，终止行号，终止列号（都是从1开始）。 如果要读的行上，列号不合法将抛出越界异常
	 */
	public static String getSouceCode(String path, int beginline, int begincolumn,
			int endline, int endcolumn) {
		LineNumberReader os = null;
		String line = null;
		StringBuffer buff = new StringBuffer();
		// 判断参数合法性
		if ((beginline > endline)
				|| (beginline == endline && begincolumn > endcolumn)) {
			return "";
		}
		if(path == null || path.equals("") ||
				path.matches(InterContext.SRCFILE_POSTFIX) || path.matches(InterContext.INCFILE_POSTFIX)){
			return "";
		}
		try {
			os = new LineNumberReader(new FileReader(path));
			// 跳到起始行处
			do {
				line = os.readLine();
			} while (line != null && os.getLineNumber() < beginline);

			// 添加起始行上的源码到buff
			if (line != null) {
				if (begincolumn > line.length()) {
					begincolumn  = 1;
				}
				if (beginline == endline) {
					try {
					buff.append(line.substring(begincolumn - 1, endcolumn>line.length()?line.length():endcolumn));
					} catch (Exception e) {
						System.out.println(begincolumn + " " + endcolumn + " " + line.length());
						e.printStackTrace();
					}
				} else {
					buff.append(line.substring(begincolumn - 1));
				}
			}

			// 如果起始行和终止行不在同一行则继续读
			while (line != null && os.getLineNumber() < endline) {
				line = os.readLine();
				buff.append("\n");
				if (os.getLineNumber() == endline) {
					buff.append(line.substring(0, endcolumn>line.length()?line.length():endcolumn));
				} else {
					buff.append(line);
				}
			}

		} catch (IOException e) {
			e.printStackTrace();
		} finally {
			if (os != null) {
				try {
					os.close();
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
		}
		return buff.toString();
	}

	/**
	 * 根据参数读取源码信息，文件路径，起始行号，终止行号， 如果要读的行上不合法将抛出越界异常
	 */
	public static String getSouceCode(String path, int beginline, int endline) {
		LineNumberReader os = null;
		String line = null;
		StringBuffer buff = new StringBuffer();
		// 判断参数合法性
		if (beginline > endline) {
			return "";
		}
		if(path == null || path.equals("") ||
				path.matches(InterContext.SRCFILE_POSTFIX) || path.matches(InterContext.INCFILE_POSTFIX)){
			return "";
		}
		try {
			os = new LineNumberReader(new FileReader(path));
			// 跳到起始行处
			do {
				line = os.readLine();
			} while (line != null && os.getLineNumber() < beginline);

			// 添加起始行上的源码到buff
			if (line != null) {
				if (beginline == endline) {
					buff.append(line);
				} else {
					buff.append(line);
				}
			}

			// 如果起始行和终止行不在同一行则继续读
			while (line != null && os.getLineNumber() < endline) {
				line = os.readLine();
				buff.append("\n");
				buff.append(line);
			}

		} catch (IOException e) {
			e.printStackTrace();
		} finally {
			if (os != null) {
				try {
					os.close();
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
		}
		return buff.toString();
	}
	
	
	public void saveProjStat(ProjectStat projStat) {
		dbcon = openDataBase(projStat.getResultdb(), TEMPLATE_MDB_PATH);
		statistics(projStat);
		closeDataBase();
		if (statcon != null) {
			try {
				statcon.close();
			} catch (SQLException ex) {
				//ex.printStackTrace();
				throw new RuntimeException("Access database connect error5",ex);
			}
		}
		statcon = null;
	}
	
	private void statistics(ProjectStat projStat) {
		statcon = openDataBase(STAT_MDB_PATH, STAT_TEMPLATE_MDB_PATH);

		String date = (new Date()).toString().replace(' ', '_');

		exportStatisticsAll(projStat.getName(),
							date,
							projStat.getTime(),
							projStat.getSyntaxTreeTime(),
							projStat.getSymbolTableTime(),
							projStat.getGlobalAnalysisTime(),
							"C",
							Config.version,
							projStat.getFileNum(),
							projStat.getTimeOutfiles(),
							projStat.getLineCnt(),
							projStat.getIpNum(),
							0);

		int scanid = getMaxScanId();
		Map ipstat = getIpCountByCategory();
		for (Object obj : ipstat.keySet()) {
			String key = (String) obj;
			String keys[] = key.split(" ");
			String defect = keys[0];
			String category = keys[1];
			exportStatistics(projStat.getName(),
							 date,
							 projStat.getTime(),
							 "C",
							 Config.version,
							 projStat.getFileNum(),
							 projStat.getLineCnt(),
							 defect,
							 category,
							 (Integer)ipstat.get(key),
							 0,
							 scanid);
		}
	}
	private String getPassword() {
		return Config.DB_STAT_PASSWORD;
	}
	/**
	 * 向数据库输出分析结果
	 * add by cjie
	 */
	public boolean writeResult(int useTime, int fileCount, int lineCount) {
		PreparedStatement select = null;
		PreparedStatement pstmt = null;
		if (dbcon == null) {
			throw new RuntimeException("database connection closed.");
		}
		try {
			String sql="delete from total";
			select = dbcon.prepareStatement(sql);
			select.executeUpdate();
			
			String strSQL="";
			// 预编译指令
			strSQL="insert into total (usetime,filecount,linecount) values (?,?,?)";

			pstmt = dbcon.prepareStatement(strSQL);
			// 设置插入的值
			pstmt.setInt(1, useTime);
			pstmt.setInt(2, fileCount);
			pstmt.setInt(3, lineCount);
			// 插入
			pstmt.executeUpdate();
		} catch (SQLException ex) {
			ex.printStackTrace();
			throw new RuntimeException("Access database connect error",ex);
		} finally {
			if (select != null) {
				try {
					select.close();
				} catch (SQLException ex) {
					throw new RuntimeException("Access database connect error",ex);
				}
			}
			if (pstmt != null) {
				try {
					pstmt.close();
				} catch (SQLException ex) {
					throw new RuntimeException("Access database connect error",ex);
				}
			}
		}
		return true;
	}

}
