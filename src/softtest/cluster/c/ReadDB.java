/**
 * 
 */
package softtest.cluster.c;

import java.io.File;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.ResultSetMetaData;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Properties;

import softtest.database.c.DBAccess;
import softtest.dscvp.c.DSCVPElement;
import softtest.scvp.c.Position;
import softtest.scvp.c.SCVP;
import softtest.scvp.c.SCVPString;
import softtest.symboltable.c.NameOccurrence;

/**
 * @author：JJL
 * @date: 2016年10月10日
 * @description:
 */
public class ReadDB {
	public String dbPath;
	private HashMap<SCVPString, DSCVPElement> D;
	private HashMap<String, DSCVPElement> DIP;
	
	public ReadDB() {
		
	}
	
	public void setDSCVP(HashMap<SCVPString, DSCVPElement> dscvpElementList) {
		this.D = dscvpElementList;
	}
	
	public  HashMap<SCVPString, DSCVPElement> getSCVP() {
		return this.D;
	}
	
	public void setDIP(HashMap<String, DSCVPElement> DIPList) {
//		HashMap<String, DSCVPElement> map = new HashMap<String, DSCVPElement>();
//		for (Entry<StringBuilder, DSCVPElement> entry : DIPList.entrySet()) { 
//			StringBuilder sb = entry.getKey();
//			DSCVPElement droot = entry.getValue();
//			map.put(sb.toString(), droot);
//		}
		this.DIP = DIPList;
	}
	
	public HashMap<String, DSCVPElement> getDIP() {
		return this.DIP;
	}
	
	public DSCVPElement getDipByString(String Num, String Variable, String F, String File, String Method, String IPLine) {
		DSCVPElement eroot = null;
		HashMap<String, DSCVPElement> map = getDIP();
		String s = F;
		if (map.containsKey(F)) {
			eroot = map.get(F);
		}
		if (eroot != null) {
			System.out.println(Num +"-find");
		} else {
			System.out.println(Num + "-none");
		}
		return eroot;
	}

	public  DSCVPElement generateFeature(String Num, String Variable, String F, String File, String Method, String IPLine) {
		DSCVPElement eroot = null;
		HashMap<SCVPString, DSCVPElement> dMap = getSCVP();
		//去掉File中路径，保留文件名
		for (int i = File.length()-1; i >= 0; i--) {
			if (File.charAt(i) == '\\') {
				File = File.substring(i+1, File.length());
				break;
			}			
		}
		// 找到集合中指定IP的定值scvp
		for (Entry<SCVPString, DSCVPElement> entry : dMap.entrySet()) { 
			SCVPString root = entry.getKey();
			if (root != null) {
				List<String> occs = root.getOccs();
				String rVariable = null;
				String rIPLine = null;
				if (occs != null && occs.size() > 0) {
					String str = occs.get(0);
					rVariable = str.substring(0, str.indexOf(":"));
					rIPLine = str.substring(str.indexOf(":")+1, str.length());
				}
				String rFile = root.getPosition().getfileName();
				String rMethod = root.getPosition().getfunctionName();
				if (isEqual(Variable, rVariable) && isEqual(File, rFile) && isEqual(Method, rMethod) && isEqual(IPLine, rIPLine)) {
					eroot = entry.getValue();
					System.out.println("!!!!JJL-- "+ Num + " 的DSCVPElement");
					return eroot;
				}
				
			}
			
		}
		System.out.println("!!!!JJL--寻找 "+ Num + " 的DSCVPElement，为null");
		return null;
	}

	public boolean isEqual(String a, String b) {
		if (a != null && b != null) {
			if (a.equals(b)) {
				return true;
			}
		}
		return false;
	}
	
	public void readFileACCESS(File mdbFile) {
		Properties prop = new Properties();
		prop.put("charSet", "gb2312"); // 这里是解决中文乱码
		prop.put("user", "");
		prop.put("password", "");
		String url = "jdbc:odbc:driver={Microsoft Access Driver (*.mdb)};DBQ="
				+ mdbFile.getAbsolutePath();
		Statement stmt = null;
		String tableName = null;
		try {
			Class.forName("sun.jdbc.odbc.JdbcOdbcDriver");
			// 连接到mdb文件
			Connection conn = DriverManager.getConnection(url, prop);
			ResultSet tables = conn.getMetaData().getTables(
					mdbFile.getAbsolutePath(), null, null,
					new String[] { "TABLE" });
			// 获取第一个表名
			if (tables.next()) {
				tableName = tables.getString(3);
			} else {
				return;
			}
			stmt = (Statement) conn.createStatement();
			/* 对结果集中每一个Variable！=null的IP进行查找 */
			String sql = "select * from IP";
			PreparedStatement ps = conn.prepareStatement(sql);
			ResultSet rset = null;
			rset = ps.executeQuery();
			ResultSetMetaData data = rset.getMetaData(); // 返回rs表结构
			int rowLength = data.getColumnCount();

			java.util.List<SimpleBean> dbList = new java.util.ArrayList<SimpleBean>();
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
				
				//DSCVPElement eroot = generateFeature(Num, Variable, stringF, File, Method, IPLine);
				DSCVPElement eroot = getDipByString(Num, Variable, stringF, File, Method, IPLine);
				SimpleBean sb = new SimpleBean(Num, Fault, Category, Variable, stringF, eroot, Equal, Related, File, Method, StartLine, IPLine);
				dbList.add(sb);
			}
			System.out.println(dbList.size());
			//setDbEmpty(dbList, conn, "Equal");
			
			Cluster c = new Cluster();
			//c.startCluster(dbList, conn);
//			// 计算等价关系,增加cluster类,jjl,2016-11-15
			
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	public static void setDbEmpty(List<SimpleBean> dbList, Connection conn, String  attribute) {
		if (dbList != null && dbList.size() > 0) {
			for (int i = 0; i < dbList.size(); i++) {
				SimpleBean listSB = dbList.get(i);
				String ls = listSB.getEqual();
				listSB.setEqual("");
				System.out.println(listSB.getNum() + listSB.getEqual());
				String sqlInsert = null;
				if (attribute.equals("Equal")) {
					sqlInsert = "update IP set Equal = ? where Num = ?";
				} else if (attribute.equals("Relate")) {
					sqlInsert = "update IP set Related = ? where Num = ?";
				}
				PreparedStatement psInsert;
				try {
					psInsert = conn.prepareStatement(sqlInsert);
					psInsert.setString(1, listSB.getEqual());
					psInsert.setString(2, listSB.getNum());
					int updateNum = psInsert.executeUpdate();
				} catch (SQLException e) {
					System.out.println("error");
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
		}
	}
	
//	public void startCluster(HashMap<String, DSCVPElement> DipList, String dbPath) {
//	//	public void startCluster(HashMap<SCVPString, DSCVPElement> dscvpElementList, String dbPath) {
//		//setDSCVP(dscvpElementList);
//		setDIP(DipList);
//		readFileACCESS(new File(dbPath));
//	}
	
	public void start(List<SimpleBean> dbList, DBAccess dbAccess) {
		Cluster c = new Cluster();
		c.startCluster(dbList, dbAccess);
	}
	
	//added by cmershen,2017.3.16,添加依赖链
	public void generateDepChain(List<SimpleBean> dbList, DBAccess dbAccess) {
		for(int i=1;i<=160;i++) {
			try {
				SimpleBean b = dbList.get(i-1);
				System.out.printf("正在生成第%d个IP的输入域：\n", i);
				HashMap<String, HashSet<DSCVPElement>> map = b.getF().getChild();
				for(String key : map.keySet()) { //每个key对应图的一个节点
					DepGraphNode g = new DepGraphNode(key);
					dfs(g,map.get(key));
					g.printDepChain();
				}
			} catch (Exception e) {
				
			}
			
		}
	}
	
	
	private void dfs(DepGraphNode g, HashSet<DSCVPElement> childSet) {
		for(DSCVPElement e : childSet) {
			HashMap<String, HashSet<DSCVPElement>> map = e.getChild();
			if(map.keySet() == null || map.keySet().size() == 0) {
				DepGraphNode child = new DepGraphNode("{S="+e.getSCVP().getStructure()+", C="+e.getSCVP().getConstants()+", V="+e.getSCVP().getVar()+", P="+e.getSCVP().getPosition()+"}");
				g.getChild().add(child);
			}
			for(String key : map.keySet()) {
				DepGraphNode child = new DepGraphNode(key);
				g.getChild().add(child);
				dfs(child, map.get(key));
			}
		}
	}


	@SuppressWarnings("unused")
	private class DepGraphNode {
		private String occ;
		private List<DepGraphNode> child;

		public DepGraphNode(String occ) {
			this.occ=occ;
			child = new ArrayList<ReadDB.DepGraphNode>();
		}
		public void printDepChain() {
			this.dfs(this, occ);
		}
		private void dfs(DepGraphNode node,String path) {
			if(node==null || node.child==null || node.child.size()==0) {
				System.out.println(path);
			}
			else {
				for(DepGraphNode child : node.child) {
					String path2 = path+"->"+child.occ;
					dfs(child, path2);
				}
			}
		}
		public String getOcc() {
			return occ;
		}
		public void setOcc(String occ) {
			this.occ = occ;
		}
		public List<DepGraphNode> getChild() {
			return child;
		}
		public void setChild(List<DepGraphNode> child) {
			this.child = child;
		}
		@Override
		public String toString() {
			return "[occ=" + occ + ", child=" + child + "]";
		}
	}
}
