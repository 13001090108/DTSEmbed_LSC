package softtest.fsmanalysis.c;

import static org.junit.Assert.fail;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.Map.Entry;
import org.apache.log4j.Logger;

import softtest.DefUseAnalysis.c.DUAnalysisVisitor;
import softtest.ast.c.*;
import softtest.callgraph.c.CGraph;
import softtest.callgraph.c.CVexNode;
import softtest.callgraph.c.DumpCGraphVisitor;
import softtest.cfg.c.ControlFlowData;
import softtest.cfg.c.ControlFlowVisitor;
import softtest.cluster.c.SimpleBean;
import softtest.config.c.Config;
import softtest.config.c.SuccessRe;
import softtest.database.c.DBAccess;
import softtest.domain.c.analysis.ControlFlowDomainVisitor;
import softtest.dscvp.c.DSCVP;
import softtest.dscvp.c.DSCVPElement;
import softtest.dscvp.c.GenerateDSCVP;
import softtest.dts.c.DTSC;
import softtest.fsm.c.FSMLoader;
import softtest.fsm.c.FSMMachine;
import softtest.fsmanalysis.c.AnalysisElement;
import softtest.interpro.c.InterCallGraph;
import softtest.interpro.c.InterMethodVisitor;
import softtest.interpro.c.InterContext;
import softtest.pretreatment.Pretreatment;
import softtest.scvp.c.SCVPPrintVisitor;
import softtest.scvp.c.SCVPString;
import softtest.scvp.c.SCVPVisitor;
import softtest.summary.lib.c.LibManager;
import softtest.symboltable.c.*;
import softtest.tools.c.jaxen.MatchesFunction;


/**
 * <p>
 * C source file analyser, analyses the source files with the finite state machine,
 * and records the results into database.
 * </p>
 */
public class CAnalysis {
	public static String LIB_SUMMARYS_PATH;

	private static Logger logger = Logger.getRootLogger();
	
	private static List<AnalysisElement> elements;
	
	private FSMControlFlowData cfData;

	
	/** 头文件集合*/
	public static TreeSet<String> incSet = new TreeSet<String>();
	/**
	 * 分析文件时的统计数据
	 */
	private int failFileNum;
	private int percent = 0;
	//dongyk 20121023预处理的进度
	private int prePercent = 0;
	private int count = 0;
	private int limitedNum = 0;
	private Pretreatment pre;
	private List<AnalysisElement> orders;
	
	//qian-2011-02-25
	private static AnalysisElement curElement;

	
	/**
	 * 全局分析的函数调用关系图
	 */
	private InterCallGraph interCGraph;
	
	private static long syntaxTreeTime =0;
	private static long symbolTableTime =0;
	private static long globalAnalysisTime =0;
	private static int timeOutfiles =0;
	
	
	public CAnalysis(List<String>files, Map<String, String> fsmList) {
		
		cfData = new FSMControlFlowData();
		failFileNum = 0;
		
		//加载数据库配置文件中选中的自动机
		for (String fsmPath : fsmList.keySet()) {
			FSMMachine fsm = FSMLoader.loadXML(fsmPath);
			fsm.setType(fsmList.get(fsmPath));
			FSMAnalysisVisitor.addFSMS(fsm);
		}
		elements = new ArrayList<AnalysisElement>();
		for (String file : files) {
			elements.add(new AnalysisElement(file));
		}
		Collections.sort(elements);
		interCGraph = InterCallGraph.getInstance();
	}
	
	private class PreAnalysisThread extends Thread
	{
		AnalysisElement element;
		String temp;
		public PreAnalysisThread(AnalysisElement element,String temp)
		{
			this.element=element;
			this.temp=temp;
		}
		public void run()
		{
			try {
				long start = System.currentTimeMillis();
				CParser parser = CParser.getParser(new CCharStream(new FileInputStream(temp)));
				//第一步：生成抽象语法树AST
				ASTTranslationUnit astroot = parser.TranslationUnit();
				long end = System.currentTimeMillis();
				if(!Config.SKIP_PREANALYSIS){
					if(Config.PreAnalysisASTRoot){
						logger.info("预处理【1】"+element+"生成语法树的时间为："+ (double)(end-start)/1000+"(s)");
					}
				}
				
				//第二步：生成符号表（变量及作用域声明、表达式类型分析）
				start = System.currentTimeMillis();
				ScopeAndDeclarationFinder sc = new ScopeAndDeclarationFinder();
				astroot.jjtAccept(sc, null);
				OccurrenceAndExpressionTypeFinder expTypeFinder = new OccurrenceAndExpressionTypeFinder();
				astroot.jjtAccept(expTypeFinder, null);
				end = System.currentTimeMillis();
				if(!Config.SKIP_PREANALYSIS){
					if(Config.PreAnalysisSymbolTable){
						logger.info("预处理【2】"+element+"生成符号表的时间为："+ (double)(end-start)/1000+"(s)");
					}
				}
				
				//第三步：zys:进行全局函数调用分析
				start = System.currentTimeMillis();
				astroot.jjtAccept(new InterMethodVisitor(), element);
				end = System.currentTimeMillis();
				if(!Config.SKIP_PREANALYSIS){
					if(Config.PreAnalysisInterMethodVisitor){
						logger.info("预处理【3】"+element+"完成全局分析的时间为："+ (double)(end-start)/1000+"(s)");
					}
				}
				
			} catch (Exception e) {
				element.setCError(true);
				logger.error("Exception in pre process file " + element.getFileName(), e);
			} catch (Error er) {
				element.setCError(true);
				logger.error("Error in pre process file " + element.getFileName(), er);
			} finally {
				System.gc();
			}
			synchronized (cfData) {
				cfData.notify();
			}
		}
	}
	/**
	 * 对源文件进行预处理，并根据预处理的中间文件做预分析
	 * 得到工程全局的函数调用关系，以及工程中源文件的依赖关系
	 *
	 */
	public void preAnalyse() {
		if(Config.GCC_TYPE==1 || Config.ANALYSIS_I){
			String headers[]=Config.LIB_HEADER_PATH.split(";");
			for(int i=0;i<headers.length;i++){
				Pretreatment.systemInc.add(headers[i]);
			}
		}
		int index=0;
		for(AnalysisElement element : elements) {
			String fileName = element.getFileName();
			String temp = null;
			//zh 2013-05-13
			DTSC.setFileName(fileName);
			index++;
			prePercent = (((int)((index*1.0/elements.size())*100))%100 )+ 1; 
			
			if(Config.ANALYSIS_I){
				temp = fileName;
				pre.findIncludeLib(temp);
				if(!Config.SKIP_PREANALYSIS)
					logger.info("[开始预处理文件:" + fileName + "]");
			}else{
				if(!Config.SKIP_PREANALYSIS)
					logger.info("[开始预处理文件:" + fileName + "]");
				// 对源代码文件进行预处理
				temp = pre.pretreat(fileName, pre.getInclude(), pre.getMacro());
			}
			//
			if (Config.ANALYSIS_R && Config.InterFile_Simplified) {
				temp = findLib(temp);
			}
			if(Config.ANALYSIS_I ){
				if(Config.FILEREPLACE && Config.InterFile_Simplified)
					temp = findLibAndReplace(temp);
				else if(Config.FILEREPLACE && !Config.InterFile_Simplified)
					temp = fileReplace(temp);
				else if(!Config.FILEREPLACE && Config.InterFile_Simplified)
					temp = findLib(temp);
			}
			
			if (temp == null || pre.isError()) {
				failFileNum++;
				element.setCError(true);
				continue;
			}
			element.setInterFileName(temp);
			if(Config.ANALYSIS_I){
				element.setFileName( setIFileName(fileName) );
			}
			
			//是否跳过预处理阶段
			if(!Config.SKIP_PREANALYSIS){
				try {
					PreAnalysisThread thread = new PreAnalysisThread(element,temp);
					long start = System.currentTimeMillis (); 
					thread.setDaemon(true);
					
					synchronized (cfData) {
						thread.start();
						try{
							cfData.wait(Config.ASTTREE_TIMEOUT);
						}catch(InterruptedException e){
							logger.info("[Interrupt error in waiting for the ASTTREE building of File " + fileName + " for time out]");
							e.printStackTrace();
						}
					}
					long end = System.currentTimeMillis (); 
					if(end-start>=Config.ASTTREE_TIMEOUT){
						thread.stop();
						element.setCError(true);
						logger.error("[Stop the pre-analysis of File " + fileName + " for ASTTREE building time out]");
					}
				} catch (Exception e) {
					logger.error("Exception in pre-analysis: " + element, e);
				} catch (Error error) {
					logger.error("Error in pre-analysis: " + element, error);
				} finally {
					System.gc();
				}
			}
				
			// remove the .. or . directory in the file path
			try {//TODO 
				//由于linux下生成的.i文件的路径格式与windows不同，
				//所以直接分析linux 下生成的.i文件时getCanonicalPath()得到的结果会不正确,暂时先跳过这一步
				fileName = element.getFileName();
				fileName = fileName.replace('\"', ' ').trim();
				if(!Config.ANALYSIS_I){
					fileName = (new File(fileName)).getCanonicalPath();
				}
				element.setFileName(fileName);
			} catch (Exception e) {	
				logger.error("Exception in pre process file " + fileName, e);
				e.printStackTrace();
			}
			if(!Config.SKIP_PREANALYSIS){
				logger.info("[结束]\n");
//				index++;
//				prePercent = (((int)((index*1.0/elements.size())*100))%100 )+ 1; 
			}
		}
	}
	
	/**
	 * 以文件为单位分析C/c代码,进行二次遍历分析
	 * 第一次对源文件进行预处理，并对预处理得到的中间进行预分析，得到文件依赖的拓扑关系和函数调用图
	 * 第二次遍历按拓扑顺序对文件进行过程间分析
	 * 
	 * @return 分析的源代码的行数
	 */
	public int analyse(String dbfilename) {
		deleteAndCreateTemp(Config.PRETREAT_DIR);
		
		//zys:开启源文件与预处理之后文件的行号映射开关
		Config.COMPUTE_LINE_NUM=true;
		// chh 初始化不能识别而需要替换的字符串序列 
		if(Config.FILEREPLACE)
			UnknownString.setReplaceString();
		//是否跳过预处理阶段，允许一定的精度损失
		SuccessRe.check();
		preAnalyse();
		
		if (Config.USE_SUMMARY) {
			// 加载生成库函数的摘要信息
			LibManager libManager = LibManager.getInstance();
			libManager.loadLib(LIB_SUMMARYS_PATH);
			Set<MethodNameDeclaration> libDecls = libManager.compileLib(pre.getLibIncludes());
			InterContext interContext = InterContext.getInstance();
			interContext.addLibMethodDecl(libDecls);
		}
		int index = 0;
			if(!Config.SKIP_METHODANALYSIS){
				if(Config.FileAnalysisOrder)
					logger.info("正在生成文件分析次序…………");
			}
			//如果跳过预处理，则按照字母序分析所有文件
			if(Config.SKIP_PREANALYSIS){
				orders=elements;
			}else{
				orders = interCGraph.getAnalysisTopoOrder();
				//liuli：2010.8.2 
				Iterator<AnalysisElement> iterator = orders.iterator();
				while(iterator.hasNext()){
					AnalysisElement order = iterator.next();
					if(order.getInterFileName() == ""){
						iterator.remove();
					}
				}
				// 如果有的文件没有在函数调用图上出现，则直接将它们添加到拓扑列表最后
				if (orders.size() > elements.size()) {
					logger.error("文件分析次序异常：拓扑排序后的文件数大于待分析文件数。");
				}else if (orders.size() < elements.size()) {
					for (AnalysisElement element : elements) {
						boolean exist = false;
						for (AnalysisElement order : orders) {
							if (order == element) {
								exist = true;
								break;
							}
						}
						if (!exist) {
								orders.add(element);
								
						}
					}
				}
			}
		if(!Config.SKIP_METHODANALYSIS){
			if(Config.FileAnalysisOrder){
				logger.info("文件分析次序分析完成…………");
				logger.info("拓扑排序后的文件总数："+orders.size()+"\t待分析的文件总数:"+elements.size()+"\n");
				if(orders.size()!=elements.size())
					logger.error("文件分析次序异常：拓扑排序后的文件数小于待分析文件数！");
			}
		}
		
		DBAccess dbAccess = DBAccess.getInstance();
		cfData.setDB(dbAccess);
		dbAccess.openDataBase(dbfilename);
		/*xwt 2011.11.3*/
		if(Config.TRIAL_OUTPUT_ALL){
			dbAccess.openComplementDB(dbfilename.substring(0, dbfilename.indexOf("."))+"_.mdb");
		}
		String fileName = null;
		SuccessRe.check();
		index = 0;
		for(AnalysisElement element : orders) {
			index++;
			//dongyk 20121023预处理的进度 与 分析的进度 分别计算显示
			percent = ((int)(index*1.0/orders.size()*100))%100+1;
			if (element.isCError() || element.getFileName().matches(InterContext.INCFILE_POSTFIX) ) {
				continue;
			}
			
			
			if(Config.ANALYSIS_I){
			//chh 替换后的临时文件以_temp.i结尾，显示文件名时要对应到相应的源.i文件
				fileName = element.getInterFileName().replace(".temp", ".i");
			}else{
				fileName = element.getFileName();
			}
			
			// 建立新的分析线程，分析源代码
			DTSC.setFileName(fileName);
			if(!Config.SKIP_METHODANALYSIS){
				if(Config.FSMInstanceAnalysis){
					logger.info("【开始分析被测文件 " + fileName + "】");
				}
			}
			try {
				AnalysisThread thread = new AnalysisThread(element);
				long start = System.currentTimeMillis (); 
				thread.setDaemon(true);
				
				synchronized (cfData) {
					thread.start();
					try{
						cfData.wait(Config.TIMEOUT);
					}catch(InterruptedException e){
						logger.info("[Interrupt error in waiting for the analysis of File " + fileName + " for time out]");
						e.printStackTrace();
					}
				}
				long end = System.currentTimeMillis (); 
				if(end-start>=Config.TIMEOUT){
					thread.stop();
					timeOutfiles++;
					logger.info("[Stop the analysis of File " + fileName + " for time out]");
				}
			} catch (Exception e) {
				logger.error("Exception in analysis: " + element, e);
			} catch (Error error) {
				logger.error("Error in analysis: " + element, error);
			} finally {
				System.gc();
			}
			if(!Config.SKIP_METHODANALYSIS){
				logger.info("[结束]\n");
			}
//			index++;
//			//dongyk 20121023预处理的进度 与 分析的进度 分别计算显示
//			percent = ((int)(index*1.0/elements.size()*100))%100+1;
		}
		//chh  删除手工宏替换的临时文件
		for(AnalysisElement element : elements) {
			if(element.getInterFileName().endsWith(".temp")){
				File tempfile=new File(element.getInterFileName());
				tempfile.delete();
			}
		}
		if (Config.ISTRIAL) {
			trialOutput(dbAccess);
		}
		
		if(Config.STEP_TIME_TRACE){
			logger.info("生成抽象语法树共用时间: " + syntaxTreeTime+ "(ms).");
			logger.info("生成符号表共用时间: " + symbolTableTime + "(ms).");
			logger.info("全局分析共用时间: " + globalAnalysisTime + "(ms).");
		}
		
		/** ytang add 20161109*/
		//从数据库中再次读取Dip，进行二次计算
		if(Config.Cluster)
			computeDipByString(dbAccess, dbfilename);//add by JJL,2016-12-4
		
/**		
		try{
			Hashtable<Integer, String> dscvpmap = dbAccess.readDSCVP();
			for(Iterator iter=dscvpmap.keySet().iterator(); iter.hasNext(); )   {   
	            Integer key = (Integer)iter.next();   
	            String value = dscvpmap.get(key);   
	    	    Pattern pp=Pattern.compile("[A-Za-z1-9]* \\[structure=entrance of function[^\\|\\&]+\\]\\]");
	    	    Matcher mm=pp.matcher(value);
	    	    int i = 0;
	    	    String cp = new String(value);
	    	    while(mm.find()){
	    		     String scvp = mm.group(0);
	    		     int s = mm.start();
	    		     int e = mm.end();
	    		     //System.out.println(value.substring(s, e));
	    		     HashSet<SCVPString> scvps = new HashSet<SCVPString>();
	    		     GenerateDSCVP.getMethodVariableSCVP(value.substring(s, e), scvps);
	    		     StringBuilder replacement = new StringBuilder();
	    		     Iterator iter1 = scvps.iterator();
	    		     while (iter1.hasNext()){
	    		    	 SCVPString ss = (SCVPString)iter1.next();
	    		    	 replacement.append(ss.toString());
	    		     }
	    		     if (replacement.length() > 0){
	    		       String ss = cp.replace(value.substring(s, e), replacement.toString());
	    		       cp = ss;
	    		     }
	    		     System.out.println(cp);
	    	    }
	    	    dbAccess.writeDSCVP(key, cp);
	            
	        } 
		}catch(Exception e){
			e.printStackTrace();
		}
		
		dbAccess.closeDataBase();
*/		

		/*xwt 2011.11.3*/
		if(Config.TRIAL_OUTPUT_ALL){
			dbAccess.closeComplementDB();
		}
		percent = 100;
		return count;
	}
	
	/**二次计算IP定值*/
	public void computeDipByString(DBAccess dbAccess, String dbfilename) {
		List<SimpleBean> dbList = dbAccess.readAccess();
		dbAccess.closeDataBase();
		
		System.out.println("构建dblist，开始二次计算");
		for (int i = 0; i < dbList.size(); i++) {
			System.out.println("开始计算" + i);
			SimpleBean sb = dbList.get(i);
			DSCVPElement eroot = sb.getF();
			String stringF = sb.getStringF();
			if (stringF != null && stringF.contains("entrance of function")) {
				if (eroot != null) {
					//第一层没有SCVP，直接getchild
					HashMap<String, HashSet<DSCVPElement>> child = eroot.getChild();
					for (Entry<String, HashSet<DSCVPElement>> entry : child.entrySet()) {
						String key = entry.getKey();
						HashSet<DSCVPElement> value = child.get(key);
						computeDipInSet(value);
					}
				}
			}
		}

		try{
			dbAccess.openDataBase(dbfilename);
			//计算DSCVP， 并更新dblist中的stringF
			updateDSCVP(dbList);
			dbAccess.writeAccessToDSCVP(dbList);
		}catch(Exception e){
			e.printStackTrace();
		}
		DTSC.dbList = dbList;
		dbAccess.closeDataBase();
	}
	
	/**更新dblist中DSCVP*/
	public void updateDSCVP(List<SimpleBean> dbList) {
		for (int i=0; i<dbList.size(); i++) {
			SimpleBean sb = dbList.get(i);
			DSCVPElement eroot = sb.getF();
			String DSCVPString = getStringByDSCVPElement(eroot);
			sb.setStringF(DSCVPString);
		}
	}
	
	/**根据DSCVPElement计算DSCVP*/
	public String getStringByDSCVPElement(DSCVPElement eroot) {
		if (eroot == null) 
			return null;
		DSCVP droot = new DSCVP();
		GenerateDSCVP.getDSCVP(droot, eroot);
		StringBuilder sb = new StringBuilder();
		while (droot != null){
			sb.append(droot.getDscvp().toString());
			droot = droot.getNextLayer();
		}
		return sb.toString();
	}
	
	public void computeDipInSet(HashSet<DSCVPElement> oldset) {
		if (oldset != null) {
			HashSet<DSCVPElement> newset = new HashSet<DSCVPElement>();
			for (DSCVPElement eroot: oldset) {
				computeDip(eroot, newset);
			}
			if (!newset.isEmpty()) {
				//用newset替换oldset
				oldset.clear();
				for (DSCVPElement eroot: newset) {
					oldset.add(eroot);
				}
			}
			
		}
	}
	private HashSet<DSCVPElement> visited = new HashSet<DSCVPElement>();
	public void computeDip(DSCVPElement eroot, HashSet<DSCVPElement> set) {
		if (eroot == null)
			return;
		SCVPString scvp = eroot.getSCVP();
		if (scvp != null) {
			if (scvp.getStructure().contains("entrance of function")) {
				//System.out.println(scvp.getStructure());
				HashSet<DSCVPElement> addset = new HashSet<DSCVPElement>();
				if(!visited.contains(eroot)) {
					visited.add(eroot);
					GenerateDSCVP.getMethodVariableSCVP(eroot, scvp, addset,1);
				}
				if (addset != null && !addset.isEmpty()) {
					String condition = "";
					if (scvp.getStructure().contains("#")){//包括条件定值
						String s = scvp.getStructure();
						condition = s.substring(s.indexOf("#"), s.length());
					} else if (scvp.getStructure().contains("$")) {
						String s = scvp.getStructure();
						condition = s.substring(s.indexOf("$"), s.length());
					}
					if (condition.equals("")) {
						for (DSCVPElement d : addset){//计算结果add到集合中
							set.add(d);
						}
					} else {
						for (DSCVPElement d : addset){//计算结果中的S加上condition字段
							SCVPString methodSCVP= d.getSCVP();
							String newStructure = methodSCVP.getStructure()+condition;
							SCVPString newSCVP = new SCVPString();
							newSCVP.setStructure(newStructure);
							newSCVP.setConstants(methodSCVP.getConstants());
							newSCVP.setOccs(methodSCVP.getOccs());
							newSCVP.setPosition(methodSCVP.getPosition());
							
							d.setSCVP(newSCVP);
							set.add(d);
						}
					}
					
				} else {//针对无法找到函数前置摘要的情况,保留原DSCVPElement
					set.add(eroot);
				}
				
			}
		}
		//System.out.println("如果看到这句话说明if出来了哦~~");
		HashMap<String, HashSet<DSCVPElement>> child = eroot.getChild();
		for (Entry<String, HashSet<DSCVPElement>> entry : child.entrySet()) {
			String key = entry.getKey();
			HashSet<DSCVPElement> value = child.get(key);
			computeDipInSet(value);
//			if(!visited.contains(value)) {
//				visited.add(value);
//				computeDipInSet(value);
//			}
		}
	}
	
	public long  getSyntaxTreeTime(){
		return this.syntaxTreeTime;
	}
	
	public long  getSymbolTableTime(){
		return this.symbolTableTime;
	}
	
	public long  getGlobalAnalysisTime(){
		return this.globalAnalysisTime;
	}
	
	public int getTimeoutfiles(){
		return this.timeOutfiles;
	}
	
	private String setIFileName(String fileName){
		File file=null;
		BufferedReader read=null;
		String fileNameI  = "";
		try 
		{
			file=new File(fileName);
			
			if(file.exists()){
				read = new BufferedReader(new FileReader(fileName));
				String line = null;
				line = read.readLine();
				if(line!=null && line.startsWith("#")){
					String[] infors = line.split(" ");
					fileNameI = infors[2];
				}						

				fileNameI = fileNameI.replace("//", "/").trim();
				fileNameI = fileNameI.replace("\"", "").trim();
				}
		} catch (Exception e) {
			e.printStackTrace();
		} finally{
			try {
				if(read!=null)
					read.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}	
		return fileNameI;
		
	}
	private void trialOutput(DBAccess dbAccess) {
		Map<String, Integer> counts = new HashMap<String, Integer>();
		Map<String, Integer> limiteds = new HashMap<String, Integer>();
		List<Report> reports = cfData.getReports();
		String key;
		for (Report report: reports) {
			key = report.getEclass() + "_" +report.getFsmName();
			Integer num = counts.get(key);
			if (num != null) {
				counts.put(key, new Integer(num.intValue() + 1));
			} else {
				counts.put(key, new Integer(1));
				limiteds.put(key, new Integer(0));
			}
		}
		for (Report report: reports) {
			key = report.getEclass() + "_" +report.getFsmName();
			int num = limiteds.get(key).intValue();
			if (num < Config.MAXIP && num < (int)(Config.PERCENT * counts.get(key))/100.0) {
				dbAccess.exportErrorData(report.getIPMethod(),report.getEclass(), report.getFsmName(), report.getFileName(), report.getRelatedVarName(),
						report.getBeginLine(), report.getErrorLine(), report.getDesp(),
						report.getSrcCode(), report.getPreCond(), report.getTraceInfo());
				System.out.println(report.hashCode());
				limiteds.put(key, new Integer(num + 1));
			}				
		}
		for (String key1 : limiteds.keySet()) {
			limitedNum += limiteds.get(key1).intValue();
		}
		/*xwt 2011.11.3*/
		if(Config.TRIAL_OUTPUT_ALL){
			List<Report> all_reports = cfData.getAllReports();
			for (Report report: all_reports) {
				dbAccess.exportErrorData(report.getIPMethod(),report.getEclass(), report.getFsmName(), report.getFileName(), report.getRelatedVarName(),
						report.getBeginLine(), report.getErrorLine(), report.getDesp(),
						report.getSrcCode(), report.getPreCond(), report.getTraceInfo());
			}
		}
	}
	
	public int progress() {
		return percent;
	}
	
	public int preProgress() {
		return prePercent;
	}
	
	public List<Report> getReports() {
		return cfData.getReports();
	}
	
	public int getFailFileNum() {
		return failFileNum;
	}
	
	public int getErrorNum() {
		return cfData.errorNum;
	}
	
	public int getReportNum() {
		if (Config.ISTRIAL) {
			return limitedNum; 
		}
		return getErrorNum();
	}
	
	public static boolean needScan(String fileName1, String fileName2) {
		if (fileName2 == null || fileName2.trim().length() == 0) {
			return true;
		}
		// 不分析系统头文件中的函数定义
//		if (fileName2.matches(InterContext.INCFILE_POSTFIX)) {
//			return !Pretreatment.isSysInc(fileName2);
//		}
		String fileName11 = fileName1.replace('"', ' ').trim();
		// if the file name contain chineset chars, we just check the postfix of the path
		if (fileName2.contains("\\\\") && !fileName2.endsWith(".h")) {
			return true;
		}
		String[] temp1 = fileName2.split("/|\\\\");
		String[] temp2 = fileName11.split("/|\\\\");
		if (temp1[temp1.length - 1].contains(temp2[temp2.length - 1])) {
			return true;
		}
		return fileName11.equals(fileName2);
	}
	
	/**
	 * 删除已有的temp目录，然后创建一个新的空的temp目录
	 */
	public static void deleteAndCreateTemp(String tempDirPath){
		File file=new File(tempDirPath);
		if(file.exists()){
			try{
				deleteDirectory(file);
			}catch(IOException e){	
				fail("fail to delete temp file");
			}
		}
		
		file=new File(tempDirPath);
		file.mkdirs();
	}
	
	/**
	 * 删除一个目录及其包含的所有内容
	 * @param dir 目录名
	 * @throws IOException 删除失败
	 */
	
	private static void deleteDirectory(File dir) throws IOException {
		if ((dir == null) || !dir.isDirectory()) {
			throw new IllegalArgumentException("Argument " + dir
					+ " is not a directory. ");
		}
		File[] entries = dir.listFiles();
		int sz = entries.length;
		for (int i = 0; i < sz; i++) {
			if (entries[i].isDirectory()) {
				deleteDirectory(entries[i]);
			} else {
				entries[i].delete();
			}
		}
		dir.delete();
	}

	class AnalysisThread extends Thread {
		//Test:单例模式是否会减少线程执行开销，提高效率？
		
		private FSMAnalysisVisitor analyser;
		private AnalysisElement element;
		
		public AnalysisThread(AnalysisElement element) {
			this.element = element;
			analyser = new FSMAnalysisVisitor(cfData);
		}
		
		@Override
		public void run() {
			try {
				doAnalyse(element); 
			} catch (ParseException e) {
				logger.error("Unknown exception when parsing the source file :" + element.getFileName(), e);
			} catch (RuntimeException e) {
				logger.error("Unknown exception when analysing the source file :" + element.getFileName(), e);
			} catch (ThreadDeath td) {
				logger.info("[Analysis thread for File " + element.getFileName() + " stop for time out]");
			} catch (Error error) {
				logger.error("Unknown error when analysing the source file :" + element.getFileName(), error);
			} catch (Exception e) {
				e.printStackTrace();
			} 
			
			synchronized (cfData) {
				cfData.notify();
			}
		}
		
		/**
		 * 预处理完成后，正式对源文件进行分析检测
		 * @param element
		 * @throws Exception
		 */
		
		private void doAnalyse(AnalysisElement element) throws Exception {
			SuccessRe.check();
			long start = System.currentTimeMillis();
			CParser parser = CParser.getParser(new CCharStream(new FileInputStream(element.getInterFileName())));
			//第一步：生成抽象语法树AST
			ASTTranslationUnit astroot = parser.TranslationUnit();
			long end = System.currentTimeMillis();
			if(!Config.SKIP_METHODANALYSIS){
				if(Config.MethodAnalysisASTRoot)
					logger.info("分析【1】"+"生成语法树的时间为："+ (double)(end-start)/1000+"(s)");
			}
			syntaxTreeTime += end-start;
			
			//qian-2011-02-25
			curElement = element;
			
			//第二步：生成符号表（变量及作用域声明、表达式类型分析）
			start = System.currentTimeMillis();
			ScopeAndDeclarationFinder sc = new ScopeAndDeclarationFinder();
			astroot.jjtAccept(sc, null);
			OccurrenceAndExpressionTypeFinder expTypeFinder = new OccurrenceAndExpressionTypeFinder();
			astroot.jjtAccept(expTypeFinder, null);
			end = System.currentTimeMillis();
			if(!Config.SKIP_METHODANALYSIS){
				if(Config.MethodAnalysisSymbolTable)
					logger.info("分析【2】"+"生成符号表的时间为："+ (double)(end-start)/1000+"(s)");
			}
			symbolTableTime += end-start;
			
			//第三步：zys:进行全局函数调用分析
			start = System.currentTimeMillis();
			astroot.jjtAccept(new InterMethodVisitor(), element);
			end = System.currentTimeMillis();
			if(!Config.SKIP_METHODANALYSIS){
				if(Config.MethodAnalysisInterMethodVisitor)
					logger.info("分析【3】"+"全局分析的时间为："+ (double)(end-start)/1000+"(s)");
			}
			globalAnalysisTime += end-start;
			
			//第四步：生成函数调用关系图，并打印
			if(!Config.SKIP_METHODANALYSIS){
				if(Config.MethodAnalysisInterMethodVisitor){
					logger.info("分析【4】生成文件内函数调用关系图开始……");
				}
			}
			
			start = System.currentTimeMillis();
			CGraph g = new CGraph();
			((AbstractScope)(astroot.getScope())).resolveCallRelation(g);
			List<CVexNode> list = g.getTopologicalOrderList(element);
			Collections.reverse(list);
			//改用新的文件的函数信息输出形式
			//dump(g, list);
			end = System.currentTimeMillis();
			if(!Config.SKIP_METHODANALYSIS){
				if(Config.MethodAnalysisInterMethodVisitor)
					logger.info("分析【4】"+"生成文件内函数调用关系图结束，所用的时间为："+ (double)(end-start)/1000+"(s)");
			}
			
			//第五步：生成控制流图
			start = System.currentTimeMillis();
			ControlFlowVisitor cfv = new ControlFlowVisitor(element.getFileName());
			ControlFlowData flow = new ControlFlowData();
			for (CVexNode cvnode : list) {
				SimpleNode node = cvnode.getMethodNameDeclaration().getNode();
				if (node instanceof ASTFunctionDefinition) {
					cfv.visit((ASTFunctionDefinition)node, flow);
				} 
			}
			end = System.currentTimeMillis();
			if(!Config.SKIP_METHODANALYSIS){
				if(Config.MethodAnalysisControlFlowVisitor)
					logger.info("分析【5】"+"生成控制流图的时间为："+ (double)(end-start)/1000+"(s)");
			}
			if(!Config.HW_RULES_CUT){
				//第六步：计算定义使用链
				if(!Config.SKIP_METHODANALYSIS){
					if(Config.MethodAnalysisDUAnalysisVisitor){
						logger.info("分析【6】计算定义使用链开始……");
					}
				}
				
				start = System.currentTimeMillis();
				astroot.jjtAccept(new DUAnalysisVisitor(), null);
				end = System.currentTimeMillis();
				if(!Config.SKIP_METHODANALYSIS){
					if(Config.MethodAnalysisDUAnalysisVisitor)
						logger.info("分析【6】"+"计算定义使用链结束，所用的时间为："+ (double)(end-start)/1000+"(s)");
				}
				//DUStatistics.print();
				//第七步：进行区间分析
				if(!Config.SKIP_METHODANALYSIS){
					if(Config.MethodAnalysisDomainVisitor){
						logger.info("分析【7】进行区间分析开始……");
					}
				}
				
				start = System.currentTimeMillis();
				ControlFlowDomainVisitor cfd = new ControlFlowDomainVisitor();
				int i=1;
				for (CVexNode cvnode : list) {
					
					long start1 = System.currentTimeMillis();
					if(!Config.SKIP_METHODANALYSIS){
						if(Config.MethodAnalysisDomainVisitor)
							logger.info("["+i+"]区间{"+cvnode.getName()+"}分析开始……");
					}
					SimpleNode node = cvnode.getMethodNameDeclaration().getNode();
					if (node instanceof ASTFunctionDefinition) {
						cfd.visit((ASTFunctionDefinition)node, null);
					} 
					end = System.currentTimeMillis();
					if(!Config.SKIP_METHODANALYSIS){
						if(Config.MethodAnalysisDomainVisitor)
							logger.info("["+i+"]区间{"+cvnode.getName()+"}分析结束，该区间分析所用的时间为："+ (double)(end-start1)/1000+"(s)");
						++i;
					}
				}
				end = System.currentTimeMillis();
				if(!Config.SKIP_METHODANALYSIS){
					if(Config.MethodAnalysisDomainVisitor)
						logger.info("分析【7】"+"进行区间分析结束，所用的时间为："+ (double)(end-start)/1000+"(s)");
				}
			}
			//if(Config.Cluster) {
				//add by cmershen,2016.5.3 区间分析结束后进行SCVP模型分析
				start = System.currentTimeMillis();
				logger.info("分析【7'】计算SCVP定值模型分析开始……");
				astroot.jjtAccept(new SCVPVisitor(), null);
	//			for (CVexNode cvnode : list) {
	//				SimpleNode node = cvnode.getMethodNameDeclaration().getNode();
	//				if (node instanceof ASTFunctionDefinition) {
	//					System.out.println(cvnode.toString());
	//					node.jjtAccept(new SCVPVisitor(), null);
	//				} 
	//			}
				
				end = System.currentTimeMillis();
				logger.info("分析【7'】计算SCVP定值模型结束，所用的时间为："+ (double)(end-start)/1000+"(s)");
				//add by cmershen,2016.8.1
				
				start = System.currentTimeMillis();
				logger.info("分析【7.1】输出SCVP定值信息开始……");
//				for (CVexNode cvnode : list) {
//					SimpleNode node = cvnode.getMethodNameDeclaration().getNode();
//					if (node instanceof ASTFunctionDefinition) {
//						System.out.println(cvnode.toString());
//						node.jjtAccept(new SCVPPrintVisitor(), null);
//					} 
//				}
				end = System.currentTimeMillis();
				logger.info("分析【7.1】输出SCVP定值信息结束，所用的时间为："+ (double)(end-start)/1000+"(s)");
			//}
//			astroot.jjtAccept(new NPDGenerateVisitor(), cfData);
//			astroot.jjtAccept(new IAOGenerateVisitor(), cfData);
//			astroot.jjtAccept(new OOBGenerateVisitor(), cfData);
			//第八步：自动机分析
			MatchesFunction.registerSelfInSimpleContext();
			if(Config.ANALYSIS_I){
				String fileName = element.getInterFileName();
				cfData.setParseFileName(getIFilePath(fileName));
			}else{
				cfData.setParseFileName(element.getFileName());
			}
			
			cfData.srcFileLine = 0;
			if(!Config.SKIP_METHODANALYSIS){
				if(Config.FSMInstanceAnalysis){
					logger.info("分析【8】开始进行自动机分析……");
				}
			}
			start = System.currentTimeMillis();
			//added by liuyan 2015/11/4
			ArrayList<String> funcList = new ArrayList<String>();
			for(CVexNode vNode : list){
				String string = vNode.getName();
				String string2[] = vNode.getName().split("_");
				StringBuffer temp = new StringBuffer();
				for(int i=0; i<string2.length-2;++i){
					temp.append(string2[i]);
					if(i != string2.length-3){
						temp.append("_");
					}
				}
				funcList.add(temp.toString());
//				funcList.add(string.substring(0,string.length()-4));
			}
			if(!Config.SKIP_METHODANALYSIS){
				if(Config.FSMInstanceAnalysis){
					logger.info("本次自动机分析的函数为："+funcList);
				}
			}
		
			//123
			astroot.jjtAccept(analyser, cfData);
			
			end = System.currentTimeMillis();
			if(!Config.SKIP_METHODANALYSIS){
				if(Config.FSMInstanceAnalysis){
					logger.info("分析【8】"+"自动机分析结束，所用的时间为："+ (double)(end-start)/1000+"(s)");
				}
			}
			if(Config.FSM_STATISTIC)
				logger.info("未释放的自动机："+FSMMachine.statistic);
			count += cfData.srcFileLine;
			if (!Config.SKIP_METHODANALYSIS){
				logger.info(element+" 分析文件行数为: " + cfData.srcFileLine);
				
			}

		}
		
		private void dump(CGraph g, List<CVexNode> list) {
			if(!Config.SKIP_METHODANALYSIS || Config.TRACE){
				if (Config.CallGraph || Config.TRACE) 
				{
					for(CVexNode n:list){
						System.out.print(n.getName()+"  ");
					}
					System.out.println();
					
					String name ="temp/FileInterCallGraph_" + element.getFileName().substring(element.getFileName().lastIndexOf("\\")+1, element.getFileName().lastIndexOf("."));
					g.accept(new DumpCGraphVisitor(), name + ".dot");
					
					if(!Config.SKIP_METHODANALYSIS){
						if(Config.MethodAnalysisInterMethodVisitor){
							if(Config.CallGraph){
								logger.info("【4 文件内函数调用】关系图输出到了文件" + name + ".dot");
							}
						}
					}
					
					System.out.println("文件内函数调用关系图输出到了文件" + name + ".dot");
					try {
						java.lang.Runtime.getRuntime().exec("dot -Tjpg -o " + name + ".jpg " + name + ".dot").waitFor();
					} catch (IOException e1) {
						System.out.println(e1);
						logger.error("请安装程序Graphvix后再运行程序");
						logger.error(e1);
					} catch (InterruptedException e2) {
						System.out.println(e2);
						logger.error("请安装程序Graphvix后再运行程序");
						logger.error(e2);
					}
					
					if(!Config.SKIP_METHODANALYSIS){
						if(Config.MethodAnalysisInterMethodVisitor){
							if(Config.CallGraph){
								logger.info("【4 文件内函数调用】关系图打印到了文件" + name + ".jpg");
							}
						}
					}
					
					System.out.println("文件内函数调用关系图打印到了文件" + name + ".jpg");
				}
			}
		}
		
		private String getIFilePath(String fileName){
			File file=null;
			BufferedReader read=null;
			String filetemp = "",temp1 = "",temp2 = "";
			try 
			{
				file=new File(fileName);			
				if(file.exists()){
					read = new BufferedReader(new FileReader(file));
					String line = null;
					line = read.readLine();
					if(line!=null && line.startsWith("#")){
						String[] infors = line.split(" ");
						if (infors.length > 3) {
							// 路径名中带有空格
							for (int i = 2; i < infors.length; i++) {
								temp1 +=  " " + infors[i];
							}
						} else {
							temp1 = infors[infors.length - 1];
						}						
					}
					line = read.readLine();
					//TODO 溢出会是什么原因？什么情况下
					if(!line.contains("<built-in>")){
						String[] infors = line.split(" ");
						if (infors.length > 3) {
							// 路径名中带有空格
							for (int i = 2; i < infors.length; i++) {
								temp2 +=  " " + infors[i];
							}
						} 
					}
					filetemp = temp2+temp1;
					filetemp = filetemp.replace("\\\\", "\\").trim();
					filetemp = filetemp.replace("//", "/").trim();
					filetemp = filetemp.replace("\"", "").trim();
					filetemp = filetemp.replace("./", "").trim();
					}
			} catch (Exception e) {
				e.printStackTrace();
			} finally{
				try {
					if(read!=null)
						read.close();
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
			return filetemp;
		}


	}

	/**
	 * 通过DTSC入口函数的分析，得到Pretreatment的实例（编译平台：KEIL GCC）
	 * @param pre
	 */
	public void setPretreatmentInstance(Pretreatment pre) {
		this.pre=pre;
	}

	public static AnalysisElement getElement(String fileName) {
		AnalysisElement temp=new AnalysisElement(fileName);
		if(CAnalysis.elements!=null){
			for(AnalysisElement a : CAnalysis.elements){
				if(a.equals(temp)){
					temp=a;
					break;
				}
			}
		}
		return temp;
	}
	
	
	//qian-2011-02-25
	public static AnalysisElement getCurAnalyElmt() {
		return curElement;
	}
	
	
	
	/**  对目前系统不能识别的字符串进行替换
	 *
	 * @param interFile
	 * @return
	 */
	public static  String fileReplace(String interFile){
		String result=interFile;
		
		/*需要被替换的字符串*/
		Object[] definelist = UnknownString.getdefine();
		
		/*替换串*/
		Object[] replaceby = UnknownString.getreplaceBy();
		
		File inter = new File(interFile);
		result=result.replace(".i", ".temp");
		File resultFile = new File(result);
		BufferedReader read = null;
		BufferedWriter write = null;
		try {
			read = new BufferedReader(new FileReader(inter));
			write = new BufferedWriter(new FileWriter(resultFile));
			String line = null;
			while((line = read.readLine()) != null) {
				line=" "+line+" ";
				for(int i = 0; i < definelist.length; i++){
					String defStr = definelist[i].toString() , replaceStr = replaceby[i].toString();
					
					/*被替换串可能是函数形式，所以先获取函数名*/
					String funcName = "";
					if(defStr.contains("("))
						funcName = defStr.substring(0, defStr.indexOf("(")+1).trim();
					
					/*文件中出现的和被替换字符串完全一至的，直接替换，因为“（”和“）”在正则表达式中是
					 * 特殊字符，所以要加转义符“\” */
					if(line.contains(defStr) || line.trim().endsWith(defStr.trim()+";")||line.trim().endsWith(defStr.trim()+"\"")){
						defStr = defStr.replaceAll("\\(", "\\\\\\(");
						defStr = defStr.replaceAll("\\)", "\\\\\\)");
						replaceStr = replaceStr.replaceAll("\\(", "\\\\\\(");
						replaceStr = replaceStr.replaceAll("\\)", "\\\\\\)");
						
						if(line.contains(defStr))
							line = line.replaceAll(defStr, replaceStr);
						else if(line.trim().endsWith(defStr.trim()+";")){
							line = line.replace(" "+(defStr.trim())+";", replaceStr+";");
						}
						else if(line.trim().endsWith(defStr.trim()+"\"")){
							line = line.replace((defStr.trim())+"\"", replaceStr.trim()+"\"");
						}
					}
					else if(line.trim().matches(defStr+".*")){
						line = line.replaceAll(defStr, replaceStr);
						line = line.replaceAll("\\s*;\\s*", ";");
						String temp=line.substring( line.lastIndexOf(' '),line.lastIndexOf(";"));
						line = line.replaceAll(temp, "");
						line = line.replaceAll("_at_", temp+" _at_ ");
					}
					/*对于函数形式的被替换串，文件中出现的串和原始被替换串参数可能不同，首先要将被替换串defStr
					 * 和替换串replacebyStr中的参数和文件中的统一*/
					else if(defStr.contains("(") && line.contains(funcName)){
						line = line.replace(";", " ;");
						int firIndex = defStr.indexOf("("), secIndex = defStr.indexOf(")",firIndex);
						
						/*1、获取原始被替换串的函数参数*/
						String[] parOld = defStr.substring(firIndex+1,secIndex).split(",");
						
						while (line.contains(funcName)){
							defStr = definelist[i].toString() ;
							replaceStr = replaceby[i].toString();
							firIndex = line.indexOf(funcName)+funcName.length();
							/*因为参数中带括号，要根据括号成对匹配来确定参数*/
							int temp = firIndex, flag = 0;
							for(; temp<line.length(); temp++){
								if(flag==0 && line.charAt(temp) == ')'){
									secIndex = temp;
									break;
								}
								else if(flag != 0 && line.charAt(temp) == ')'){
									flag --;
								}
								else if(line.charAt(temp) == '('){
									flag ++;
								}
							}
								
							
							/*2、获取文件中的函数参数*/
							String[] parNew = line.substring(firIndex,secIndex).split(",");
							/*3、如果参数个数不一致则无法继续替换，否则用文件中的函数参数parNew将原始串中的参数替换*/
							if(parNew.length != parOld.length)
								break;
							else{
								for(int j = 0; j < parNew.length; j++){
									/*如果参数字符串前后没有空格，则加“\b”分界符匹配，以保证替换的是整个单词*/
									if(parOld[j] .startsWith(" ") && parOld[j].endsWith(" ")){
										defStr = defStr.replaceAll(parOld[j], parNew[j]);
									}
									else if(!parOld[j] .startsWith(" ") && parOld[j].endsWith(" ")){
										defStr = defStr.replaceAll("\\b"+parOld[j], parNew[j]);
									}
									else if(parOld[j] .startsWith(" ") && !parOld[j].endsWith(" ")){
										defStr = defStr.replaceAll(parOld[j]+"\\b", parNew[j]);
									}
									else if(!parOld[j] .startsWith(" ") && !parOld[j].endsWith(" ")){
										defStr = defStr.replaceAll("\\b"+parOld[j]+"\\b", parNew[j]);
									}
									String tempParOld = parOld[j].trim();
									if(!tempParOld.startsWith("\\b"))
										tempParOld = "\\b"+tempParOld;
									if(!tempParOld.endsWith("\\b"))
										tempParOld = tempParOld+"\\b";
									replaceStr = replaceStr.replaceAll(tempParOld, parNew[j]);
								}
								defStr = defStr.replaceAll("\\(", "\\\\\\(");
								defStr = defStr.replaceAll("\\)", "\\\\\\)");
								replaceStr = replaceStr.replaceAll("\\(", "\\\\\\(");
								replaceStr = replaceStr.replaceAll("\\)", "\\\\\\)");
								/*“*”也是正则表达式的特殊字符，加转义符*/
								defStr = defStr.replaceAll("\\*","\\\\\\*");
								replaceStr = replaceStr.replaceAll("\\*", "\\\\\\*");
								defStr = defStr.trim();
								/*4、替换*/
								line = line.replaceAll(defStr, replaceStr);
							}
						}
					}	
				}
				if(!line.trim().equals(""))
				line = line.trim();
				write.write(line);
				write.write("\n");
			}
		} catch (Exception e) {
			return interFile;
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
			if( write != null ){
				try {
					write.close();
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
		}
		return result;
	}
	/**简化中间处理文件，去掉多余的空行、无用行；另外获取引入的系统头文件
	 * 
	 * @param file
	 * @return
	 */
	
	public static String findLib(String file){
		String outFile = file.replace(".i", ".temp");
		File inter = new File(file);
		File outer = new File(outFile);
		BufferedReader read = null;
		BufferedWriter write = null;
		try {
			read = new BufferedReader(new FileReader(inter));
			write = new BufferedWriter(new FileWriter(outer));
			String line = null;
			String nextline = null;
			String[] fileItem, nextLineItem;
			String fileName = "", incName = null;
			StringBuffer buffer = new StringBuffer();
			boolean delete = false;
			/*获取文件名（不带具体路径）并替换为.c后缀*/
			fileItem = file.replaceAll("\"", "").split("\\\\");
			fileName = fileItem[fileItem.length-1].replace(".i", ".c");
			if(fileName.endsWith(".gcc"))
				fileName = fileName.replace(".gcc", "");
			
			while((line = read.readLine()) != null) {
				buffer.append(line);
				/* 遇到#~~filename~~~的行说明此.i文件接下来开始新的头文件展开*/
				if(line.startsWith("#") && line.contains(fileName)){
					delete = false;
					while((nextline = read.readLine())!= null){
						if(nextline.equals("")){
							buffer.append("\n"+"");
							continue;
						}
						/*再次遇到#，表示可能是一个头文件展开的开始，且#这一行包含头文件文件名*/
						if(nextline.startsWith("#"))
						{
							nextLineItem = nextline.split(" ");
							if(nextLineItem.length >= 3){
								incName = nextLineItem[2].replaceAll("\"", "");
								if(incName.endsWith(".h")){
									incName = incName.replace("\\\\", "/");
									incName = incName.replace("//", "/");
									/*如果此头文件名未加入incset，则将头文件展开部分copy到.temp文件
									 * 否则说明这个头文件已被分析过，要将此头文件展开部分删除，将delete开关设为true*/
									if(incSet.add(incName)){
										buffer.append("\n"+nextline);
									}
									else{
										buffer.delete(0, buffer.length());
										delete = true;
									}
									break;
								}
								else{
									if(!incName.equals(fileName)){
										buffer.append("\n"+nextline);
										break;
									}
									else{
										write.write(buffer.toString());
										write.write("\n");
										buffer.delete(0, buffer.length());
										buffer.append(nextline);
									}
								}
							}
							else{
								buffer.append("\n"+nextline);
								break;
							}
						}
						else{
							buffer.append("\n"+nextline);
							break;
						}
					}
					if(!delete)
					write.write(buffer.toString()+"\n");
				}
				else{
					if(!delete)
						write.write(buffer.toString()+"\n");
					buffer.delete(0, buffer.length());
					continue;
				}
				buffer.delete(0, buffer.length());
			}
		} catch (Exception e) {
			e.printStackTrace();
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
			if( write != null ){
				try {
					write.close();
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
		}
		return outFile;
	}
	/** 简化中间处理文件，去掉多余的空行、无用行；另外获取引入的系统头文件,同时进行不能识别字符串的替换
	 * 
	 * @param file
	 * @return
	 */
	public static String findLibAndReplace(String file){
		Object[] definelist = UnknownString.getdefine();
		Object[] replaceby = UnknownString.getreplaceBy();
		String outFile = file.replace(".i", ".temp");
		File inter = new File(file);
		File outer = new File(outFile);
		BufferedReader read = null;
		BufferedWriter write = null;
		try {
			read = new BufferedReader(new FileReader(inter));
			write = new BufferedWriter(new FileWriter(outer));
			String line = null;
			String nextline = null;
			String[] fileItem, nextLineItem;
			String fileName = "", incName = null;
			StringBuffer buffer = new StringBuffer();
			boolean delete = false;
			fileItem = file.replaceAll("\"", "").split("\\\\");
			fileName = fileItem[fileItem.length-1].replace(".i", ".c");
			if(fileName.endsWith(".gcc"))
				fileName = fileName.replace(".gcc", "");
			while((line = read.readLine()) != null) {
				buffer.append(line);
				if(line.startsWith("#") && line.contains(fileName)){
					delete = false;
					while((nextline = read.readLine())!= null){
						if(nextline.equals("")){
							buffer.append("\n"+"");
							continue;
						}
						if(nextline.startsWith("#"))
						{
							nextLineItem = nextline.split(" ");
							if(nextLineItem.length >= 3){
								incName = nextLineItem[2].replaceAll("\"", "");
								if(incName.endsWith(".h")){
									incName = incName.replace("\\\\", "/");
									incName = incName.replace("//", "/");
									if(incSet.add(incName)){
										buffer.append("\n"+nextline);
									}
									else{
										buffer.delete(0, buffer.length());
										delete = true;
									}
									break;
								}
								else{
									if(!incName.equals(fileName)){
										buffer.append("\n"+nextline);
										break;
									}
									else{
										buffer.replace(0, buffer.length(), fileReplaceInFindLib(buffer.toString(),definelist,replaceby)) ;
										write.write(buffer.toString());
										write.write("\n");
										buffer.delete(0, buffer.length());
										buffer.append(nextline);
									}
								}
							}
							else{
								buffer.append("\n"+nextline);
								break;
							}
						}
						else{
							buffer.append("\n"+nextline);
							break;
						}
					}
					if(!delete){
						buffer.replace(0, buffer.length(), fileReplaceInFindLib(buffer.toString(),definelist,replaceby)) ;
						write.write(buffer.toString()+"\n");
					}
				}
				else{
					if(!delete){
						buffer.replace(0, buffer.length(), fileReplaceInFindLib(buffer.toString(),definelist,replaceby)) ;
						write.write(buffer.toString()+"\n");
					}
					buffer.delete(0, buffer.length());
					continue;
				}
				buffer.delete(0, buffer.length());
			}
		} catch (Exception e) {
			e.printStackTrace();
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
			if( write != null ){
				try {
					write.close();
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
		}
		return outFile;
	}
	
	private static String fileReplaceInFindLib(String buffer,Object[] definelist,Object[] replaceby){
		String[] line = buffer.split("\n");
		String result = "";
		for(int i=0; i<line.length; i++){
			line[i] = " "+line[i]+" ";
			for(int j = 0; j < definelist.length; j++){
				String defStr = definelist[j].toString() , replaceStr = replaceby[j].toString();
				String funcName = "";
				if(defStr.contains("("))
					funcName = defStr.substring(0, defStr.indexOf("(")+1);
				if(line[i].contains(defStr)||line[i].trim().endsWith(defStr.trim()+";")){
					defStr = defStr.replaceAll("\\(", "\\\\\\(");
					defStr = defStr.replaceAll("\\)", "\\\\\\)");
					replaceStr = replaceStr.replaceAll("\\(", "\\\\\\(");
					replaceStr = replaceStr.replaceAll("\\)", "\\\\\\)");
					if(line[i].contains(defStr))
						line[i] = line[i].replaceAll(defStr, replaceStr);
					else if(line[i].trim().endsWith(defStr.trim()+";")){
						line[i] = line[i].replace(" "+(defStr.trim())+";", replaceStr+";");
					}
				}
				else if(defStr.contains("(") && line[i].contains(funcName)){
					line[i] = line[i].replace(";", " ;");
					int firIndex = defStr.indexOf("("), secIndex = defStr.indexOf(")",firIndex);
					String[] parOld = defStr.substring(firIndex+1,secIndex).split(",");
					while (line[i].contains(funcName)){
						defStr = definelist[j].toString() ;
						replaceStr = replaceby[j].toString();
						firIndex = line[i].indexOf(funcName)+funcName.length();
						int temp = firIndex, flag = 0;
						for(; temp<line[i].length(); temp++){
							if(flag==0 && line[i].charAt(temp) == ')'){
								secIndex = temp;
								break;
							}
							else if(flag != 0 && line[i].charAt(temp) == ')'){
								flag --;
							}
							else if(line[i].charAt(temp) == '('){
								flag ++;
							}
						}
							
							
						String[] parNew = line[i].substring(firIndex,secIndex).split(",");
						if(parNew.length != parOld.length)
							break;
						else{
							for(int k = 0; k < parNew.length; k++){
								if(parOld[k] .startsWith(" ") && parOld[k].endsWith(" ")){
									defStr = defStr.replaceAll(parOld[k], parNew[k]);
								}
								else if(!parOld[k] .startsWith(" ") && parOld[k].endsWith(" ")){
									defStr = defStr.replaceAll("\\b"+parOld[k], parNew[k]);
								}
								else if(parOld[k] .startsWith(" ") && !parOld[k].endsWith(" ")){
									defStr = defStr.replaceAll(parOld[k]+"\\b", parNew[k]);
								}
								else if(!parOld[k] .startsWith(" ") && !parOld[k].endsWith(" ")){
									defStr = defStr.replaceAll("\\b"+parOld[k]+"\\b", parNew[k]);
								}
								String tempParOld = parOld[k].trim();
								if(!tempParOld.startsWith("\\b"))
									tempParOld = "\\b"+tempParOld;
								if(!tempParOld.endsWith("\\b"))
									tempParOld = tempParOld+"\\b";
								replaceStr = replaceStr.replaceAll(tempParOld, parNew[k]);
							}
							defStr = defStr.replaceAll("\\(", "\\\\\\(");
							defStr = defStr.replaceAll("\\)", "\\\\\\)");
							replaceStr = replaceStr.replaceAll("\\(", "\\\\\\(");
							replaceStr = replaceStr.replaceAll("\\)", "\\\\\\)");
							defStr = defStr.replaceAll("\\*","\\\\\\*");
							replaceStr = replaceStr.replaceAll("\\*", "\\\\\\*");
							defStr = defStr.trim();
							line[i] = line[i].replaceAll(defStr, replaceStr);
						}
					}
				}	
			}
			line[i] = line[i].trim();
			result += (line[i]+"\n");
		}
		return result;
	}
}
