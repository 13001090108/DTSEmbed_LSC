package softtest.summary.lib.c;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import softtest.ast.c.ParseException;
import softtest.interpro.c.Method;
import softtest.summary.c.MethodSummary;
import softtest.summary.lib.c.LibMethodSummary;
import softtest.symboltable.c.MethodNameDeclaration;

/**
 * 
 * 库函数函数摘要管理器，负责从指定目录中加载库函数函数摘要，并编译生成函数声明，构建函数摘要
 * @author qipeng
 *
 */
public class LibManager {

	/**
	 * <p>当前从配置文件中加载的所有函数库，及库中定义的有特征信息的函数列表</p>
	 */
	private Map<String, ArrayList<LibMethodSummary>> libSummarys;
	private static LibManager instance;
	
	private LibManager() {
		libSummarys = new HashMap<String, ArrayList<LibMethodSummary>>();
	}
	
	public static LibManager getInstance() {
		if (instance == null) {
			instance = new LibManager();
		}
		return instance;
	}
	
	public void clear() {
		if (libSummarys != null) {
			libSummarys.clear();
		}
	}
	
	/**
	 * 加载指定目录下所有的配置文件描述的函数摘要信息
	 * 
	 * @param path 包含函数摘要信息的文件目录
	 */
	public void loadLib(String path) {
		File dir = new File(path);
		if(!dir.exists())
			return;
		File[] files = dir.listFiles();
		for (int i = 0; i < files.length; i++) {
			if (files[i].getName().endsWith(".xml")) {
				LibLoader.loadLibSummarys(files[i].getAbsolutePath());	
			}
		}
	}
	
	/** zys:2010.6.22 加载单个XML文件的库函数摘要*/
	public void loadSingleLibFile(String path)
	{
		String temp[]=path.split("/");
		String fileName=temp[temp.length-1];
		File dir=new File(temp[0]);
		File[] files = dir.listFiles();
		for (int i = 0; i < files.length; i++) {
			if (files[i].getName().endsWith(fileName)) {
				LibLoader.loadLibSummarys(files[i].getAbsolutePath());	
			}
		}
	}
	
	/**
	 * 添加库函数摘要信息到当前管理器中
	 * 
	 * @param libName 库函数所在库名称
	 * @param libSummary 函数摘要信息
	 */
	public void addLib(String libName, LibMethodSummary libSummary) {
		if (libName.contains(";")) {
			String[] libNames = libName.split(";");
			for (int i = 0; i < libNames.length; i++) {
				addLib(libNames[i], libSummary);
			}
		} else {
			ArrayList<LibMethodSummary> summarys = libSummarys.get(libName);
			if (summarys == null) {
				summarys = new ArrayList<LibMethodSummary>();
				summarys.add(libSummary);
				libSummarys.put(libName, summarys);
			} else {
				summarys.add(libSummary);
			}
		}
	}
	
	/**
	 * 根据当前分析引用的库，按需生成其中库的函数摘要信息
	 * 
	 * @param includeLibs 当前分析引用的库列表
	 * @return 生成的库函数的函数声明
	 * @throws ParseException 
	 */
	//20141125
	public Set<MethodNameDeclaration> compileLib(Set<String> includeLibs) {
		Map<Method, MethodNameDeclaration> libDecl = new HashMap<Method, MethodNameDeclaration>();
		for (String lib : libSummarys.keySet()) {
//			for (String include : includeLibs) {
//				int i=include.lastIndexOf('/');
//				String header=include.substring(i+1, include.length());
//				if (header.equalsIgnoreCase(lib)) { //change "include" to lower-case format by Xinhong Yao. 11/14/2009
					ArrayList<LibMethodSummary> summarys = libSummarys.get(lib);
					for (LibMethodSummary summary : summarys) {
						MethodNameDeclaration decl = summary.compileSummary();						
						if (decl != null) {
							if (libDecl.containsKey(decl.getMethod())) {
								MethodNameDeclaration oldDecl = libDecl.get(decl.getMethod());
								MethodSummary mtSummary = oldDecl.getMethodSummary();
								mtSummary.addSummary(decl.getMethodSummary());
							} else {
								libDecl.put(decl.getMethod(), decl);
							}
						}
//					}
//				}
			}
		}
		return new HashSet<MethodNameDeclaration>(libDecl.values());
	}
	//modified by liuyan 2014.9.5
//	public Set<MethodNameDeclaration> compileLib(Set<String> includeLibs) throws ParseException {
//		Map<Method, MethodNameDeclaration> libDecl = new HashMap<Method, MethodNameDeclaration>();
//		for (String lib : libSummarys.keySet()) {
//				//如果进行了中间文件化简,则加载所引用的头文件,否则全部加载存在摘要的头文件
//				for (String include : includeLibs) {
//					if (include.toLowerCase().endsWith(lib)) { //change "include" to lower-case format by Xinhong Yao. 11/14/2009
//						ArrayList<LibMethodSummary> summarys = libSummarys.get(lib);
//						for (LibMethodSummary summary : summarys) {
//							MethodNameDeclaration decl = summary.compileSummary();
//							if (decl != null) {
//								if (libDecl.containsKey(decl.getMethod())) {
//									MethodNameDeclaration oldDecl = libDecl.get(decl.getMethod());
//									MethodSummary mtSummary = oldDecl.getMethodSummary();
//									mtSummary.addSummary(decl.getMethodSummary());
//								} else {
//									libDecl.put(decl.getMethod(), decl);
//								}
//							}
//						}
//					}
//				}
//			}
//		return new HashSet<MethodNameDeclaration>(libDecl.values());
//	}
}
