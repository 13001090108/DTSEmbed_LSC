package softtest.test.keilc.rules.fault;

import static org.junit.Assert.fail;
import static org.junit.Assert.assertEquals;

import java.io.ByteArrayInputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import org.apache.log4j.BasicConfigurator;
import org.apache.log4j.PropertyConfigurator;
import org.junit.After;
import org.junit.AfterClass;
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
import softtest.symboltable.c.AbstractScope;
import softtest.symboltable.c.OccurrenceAndExpressionTypeFinder;
import softtest.symboltable.c.ScopeAndDeclarationFinder;
import softtest.test.c.rules.ModelTestBase;

@RunWith(Parameterized.class)
public class Test_VarDR {
	private String source = null;
	private String compiletype=null;
	private String result = null;
	private static final String fsmPath="softtest/rules/keilc/fault/VarDR-0.1.xml";
	FSMAnalysisVisitor fsmAnalysis; 
	private FSMControlFlowData cfData;
	
	public Test_VarDR(String source,String compiletype, String result)
	{
		this.source=source;	
		this.compiletype=compiletype;
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
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
		
		Config.REGRESS_RULE_TEST=true;
	}
	
	//根据不同的模式需求，自行分配当前AST分析到的步骤
	private void analysis(ASTTranslationUnit astroot){
		astroot.jjtAccept(new ScopeAndDeclarationFinder(), null);
		astroot.jjtAccept(new OccurrenceAndExpressionTypeFinder(), null);
		
		astroot.jjtAccept(fsmAnalysis, cfData);
		
		assertEquals(result,getFSMAnalysisResult());
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
	
	@Test
	public void test() {
		CParser.setType("gcc");
		CParser parser_gcc = CParser.getParser(new CCharStream(new ByteArrayInputStream(source.getBytes())));
		CParser.setType("keil");
		CParser parser_keil = CParser.getParser(new CCharStream(new ByteArrayInputStream(source.getBytes())));
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
	
	 @Parameters
	 public static Collection<Object[]> testcaseAndResults()
	 {
		 return Arrays.asList(new Object[][] {
////////////////	/  0   ///////////////////	
		            {
		            ""                                                                     +"\n"+
		            "#include <reg51.h>"                                                   +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "int testAddr _at_ 0x40;	 //data 	"                                    +"\n"+
		            ""                                                                     +"\n"+
		            "	"                                                                    +"\n"+
		            "void main(void)"                                                      +"\n"+
		            "{"                                                                    +"\n"+
		            "	//int test2;"                                                        +"\n"+
		            "	//int test3;"                                                        +"\n"+
		            "    //int testAddr2 _at_ 0x60;	"                                      +"\n"+
		            ""                                                                     +"\n"+
		            "	SCON=0x52;"                                                          +"\n"+
		            "	TMOD=0x20;"                                                          +"\n"+
		            "	TCON = 0x69;"                                                        +"\n"+
		            "	TH1=0xf3;"                                                           +"\n"+
		            "	EX0 = 1;"                                                            +"\n"+
		            "	EA = 1;"                                                             +"\n"+
		            "	"                                                                    +"\n"+
		            "    while(1)"                                                         +"\n"+
		            "	{"                                                                   +"\n"+
		            "		testAddr = 256;"                                                    +"\n"+
		            "	    // 如果在这里进入中断，则下一行的打印语句会出错 ……(a)"                                 +"\n"+
		            "        //"                                                           +"\n"+
		            "		printf(\"main function: %d \\n\",testAddr);"                           +"\n"+
		            "		//printf(\"Hello,world \\n\");"                                        +"\n"+
		            "	}"                                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "	//while(1) { }"                                                      +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void int0() interrupt 0 using 0"                                      +"\n"+
		            "{"                                                                    +"\n"+
		            "	"                                                                    +"\n"+
		            "	testAddr = 3;"                                                       +"\n"+
		            "	printf(\"interrupt: %d \\n\", testAddr);"                               +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "VarDR"
		            ,
		            },
			 
		 });
	 }
}
