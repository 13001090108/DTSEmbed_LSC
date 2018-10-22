package softtest.test.keilc.rules.fault;

import static org.junit.Assert.fail;
import static org.junit.Assert.assertEquals;


import java.io.FileInputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import org.apache.log4j.BasicConfigurator;
import org.apache.log4j.PropertyConfigurator;
import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import softtest.DefUseAnalysis.c.DUAnalysisVisitor;
import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.CCharStream;
import softtest.ast.c.CParser;
import softtest.ast.c.ParseException;
import softtest.callgraph.c.CGraph;
import softtest.callgraph.c.CVexNode;
import softtest.cfg.c.ControlFlowVisitor;
import softtest.config.c.Config;
import softtest.fsm.c.FSMLoader;
import softtest.fsm.c.FSMMachine;
import softtest.fsmanalysis.c.FSMAnalysisVisitor;
import softtest.fsmanalysis.c.FSMControlFlowData;
import softtest.fsmanalysis.c.Report;
import softtest.fsmanalysis.c.AnalysisElement;
import softtest.interpro.c.InterContext;
import softtest.symboltable.c.AbstractScope;
import softtest.symboltable.c.OccurrenceAndExpressionTypeFinder;
import softtest.symboltable.c.ScopeAndDeclarationFinder;
import softtest.pretreatment.PlatformType;
import softtest.pretreatment.Pretreatment;
import java.io.*;

@RunWith(Parameterized.class)
public class Test_EDD {
	
	private String compiletype = null;
	private String result = null;
	private static final String fsmPath = "softtest/rules/keilc/fault/EDD-0.1.xml";
	FSMAnalysisVisitor fsmAnalysis; 
	private FSMControlFlowData cfData;
	private String srcFilesPath=".\\testcase\\rules\\fault\\EDD\\";
	private List<String> filePathList= new ArrayList<String>();
	private static List<AnalysisElement> elements=new ArrayList<AnalysisElement>();
	private Pretreatment pre= new Pretreatment();
	
	public Test_EDD(String path,String compiletype, String result)
	{
		this.srcFilesPath=srcFilesPath+path;	
		this.compiletype=compiletype;
		if (compiletype.equals("gcc")) {
			pre.setPlatform(PlatformType.GCC);
		} else if (compiletype.equals("keil")) {
			pre.setPlatform(PlatformType.KEIL);
		}
		this.result = result;
	}

	@BeforeClass
	public static void setUpBase()
	{
		BasicConfigurator.configure();
        PropertyConfigurator.configure("log4j.properties") ;
		//根据待测试模式XML文件路径初始化自动机列表
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		
		//ZYS:最好根据状态机描述文件XML中的相关字段读取出该模式所属于的故障类别
		fsm.setType("fault");
		//每次加入自动机前都清空一下原来的fsms
		//FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
		
		Config.REGRESS_RULE_TEST=true;
	}
	
	private void collect(File srcFile) {
		if (srcFile.isFile() && srcFile.getName().matches(InterContext.SRCFILE_POSTFIX)) {
			filePathList.add(srcFile.getPath());
		} else if (srcFile.isDirectory()) {
			File[] fs = srcFile.listFiles();
			for (int i = 0; i < fs.length; i++) {
				collect(fs[i]);
			}
		}
	}
	//根据不同的模式需求，自行分配当前AST分析到的步骤
	private void analysis(ASTTranslationUnit astroot){
		astroot.jjtAccept(new ScopeAndDeclarationFinder(), null);
		astroot.jjtAccept(new OccurrenceAndExpressionTypeFinder(), null);
		
		astroot.jjtAccept(new ControlFlowVisitor(), null);

		astroot.jjtAccept(fsmAnalysis, cfData);
		
	}
	public void preAnalyse() {
		for(AnalysisElement element : elements) {
			String fileName = element.getFileName();
			String temp = null;
			temp = pre.pretreat(fileName, pre.getInclude(), pre.getMacro());
			
			if (temp == null || pre.isError()) {
				element.setCError(true);
				element.setInterFileName(element.getFileName());
				continue;
			}
			element.setInterFileName(temp);
		}
	}

	private String getFSMAnalysisResult()
	{
		List<Report> reports=cfData.getReports();
		String analysisResult=null;
		if(reports.size()==0)
		{
			analysisResult="OK";
			return analysisResult;
		}
		for(Report r:reports)
		{
			analysisResult=r.getFsmName();
			System.out.println(r.getFsmName()+" : "+r.getDesp());
		}
		//cfData.setReports(null);
		return analysisResult;
	}

	@Before
	public void init() {
		cfData = new FSMControlFlowData();
		List<Report> reports = new ArrayList<Report>();
		cfData.setReports(reports);

		fsmAnalysis=new FSMAnalysisVisitor(cfData); 	

	}

	@After
	public void shutdown() {
		//清除临时文件夹
	}
	
	
	public void analysor (AnalysisElement element) throws Exception{
		
		CParser.setType("gcc");
		CParser parser_gcc = CParser.getParser(new CCharStream(new FileInputStream(element.getInterFileName())));
		CParser.setType("keil");
		CParser parser_keil = CParser.getParser(new CCharStream(new FileInputStream(element.getInterFileName())));
		ASTTranslationUnit gcc_astroot=null,keil_astroot=null;
		if(compiletype.equals("gcc")){
			CParser.setType("gcc");
			try {
				gcc_astroot = parser_gcc.TranslationUnit();
			} catch (ParseException e) {
				e.printStackTrace();
				fail("parse error");
			}
			analysis(gcc_astroot); 
		}else if(compiletype.equals("keil")){
			CParser.setType("keil");
			try {
				keil_astroot= parser_keil.TranslationUnit();
			} catch (ParseException e) {
				e.printStackTrace();
				fail("parse error");
			}
			analysis(keil_astroot);
		}else{
			CParser.setType("gcc");
			try {
				gcc_astroot = parser_gcc.TranslationUnit();
			} catch (ParseException e) {
				e.printStackTrace();
				fail("parse error");
			}
			analysis(gcc_astroot);
			
			CParser.setType("keil");
			try {
				keil_astroot= parser_keil.TranslationUnit();
			} catch (ParseException e) {
				e.printStackTrace();
				fail("parse error");
			}
			analysis(keil_astroot);
		}
	
		
	}
	@Test
	public void test() {
		File srcFile = new File(srcFilesPath);
		if (!srcFile.exists()) {
			throw new RuntimeException("Error: File " + srcFile.getName() + " does not exist.");
		}
		collect(srcFile);
		
		for (String file : filePathList) {
			
			elements.add(new AnalysisElement(file));
		}
		preAnalyse();
		for(AnalysisElement element:elements)
		{
			try
			{
				analysor(element);
			} catch (Exception e)
			{
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		assertEquals(result,getFSMAnalysisResult());
		filePathList.clear();
		elements.clear();
	}
	 @Parameters
	 public static Collection<Object[]> testcaseAndResults()
	 {
		 return Arrays.asList(new Object[][] {
////////////////	/  0   ///////////////////	
		            {
		            
		            "test1"                                                                    
		            ,
		            "keil"
		            ,
		            "EDD"
		            ,
		            },
////////////////	/  1   ///////////////////	
		            {
		            
		            "test2"                                                                    
		            ,
		            "keil"
		            ,
		            "EDD"
		            ,
		            },
////////////////	/  1   ///////////////////	
		            {
		            
		            "test3"                                                                    
		            ,
		            "keil"
		            ,
		            "EDD"
		            ,
		            },
		 });
	 }
}