package softtest.test.keilc.rules.fault;

import static org.junit.Assert.*;

import java.io.ByteArrayInputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.CCharStream;
import softtest.ast.c.CParser;
import softtest.ast.c.ParseException;
import softtest.cfg.c.ControlFlowVisitor;
import softtest.config.c.Config;
import softtest.fsm.c.FSMLoader;
import softtest.fsm.c.FSMMachine;
import softtest.fsmanalysis.c.FSMAnalysisVisitor;
import softtest.fsmanalysis.c.FSMControlFlowData;
import softtest.fsmanalysis.c.Report;
import softtest.symboltable.c.OccurrenceAndExpressionTypeFinder;
import softtest.symboltable.c.ScopeAndDeclarationFinder;
 /**  
  * 参数化测试的类必须有Parameterized测试运行器修饰  
  * 问题：目前的回归测试没有进行预处理。。。
  *  @author zys
  */ 
@RunWith(Parameterized.class)
public class Test_RC{
	private String source = null;
	private String compiletype=null;
	private String result = null;
	private static final String fsmPath="softtest/rules/keilc/fault/RC-0.1.xml";
	private FSMAnalysisVisitor fsmAnalysis; 
	private FSMControlFlowData cfData;
	
	public Test_RC(String source,String compiletype, String result)
	{
		//System.out.println("子类构造函数：SubClass()!");
		this.source=source;	
		this.compiletype=compiletype;
		this.result = result;
	}

	@AfterClass
	public static void tearDownBase() {
		//System.out.println("@AfterClass in 子类 SubClass!");
	}
	@BeforeClass
	public static void setUpBase()
	{
		//System.out.println("@BeforeClass in 子类 SubClass!");
		//根据待测试模式XML文件路径初始化自动机列表
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		
		//ZYS:最好根据状态机描述文件XML中的相关字段读取出该模式所属于的故障类别
		fsm.setType("fault");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
		
		Config.REGRESS_RULE_TEST=true;
	}
	private void analysis(ASTTranslationUnit astroot){
		astroot.jjtAccept(new ScopeAndDeclarationFinder(), null);
		astroot.jjtAccept(new OccurrenceAndExpressionTypeFinder(), null);
		astroot.jjtAccept(new ControlFlowVisitor(), null);
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
		System.out.println("本次检测共报告了"+reports.size()+"个故障点");
		for(Report r:reports)
		{
			System.out.println("\t"+r.getFsmName()+" : "+r.getDesp());
			analysisResult=r.getFsmName();
		}
		
		return analysisResult;
	}

	@Before
	public void init() {
		//System.out.println("@Before in 子类 SubClass!");
		cfData = new FSMControlFlowData();
		List<Report> reports = new ArrayList<Report>();
		cfData.setReports(reports);
		fsmAnalysis=new FSMAnalysisVisitor(cfData); 
	}

	@After
	public void shutdown() {
		//清除临时文件夹
		//System.out.println("@After in 子类 SubClass!");
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
	
	/**  
	#      * 准备数据。数据的准备需要在一个方法中进行，该方法需要满足一定的要求：  
	#   
	#          1）该方法必须由Parameters注解修饰  
	#          2）该方法必须为public static的  
	#          3）该方法必须返回Collection类型  
	#          4）该方法的名字不做要求  
	#          5）该方法没有参数  
	#      * @return  
	#      */  
	 @Parameters
	 public static Collection<Object[]> testcaseAndResults()
	 {
		 return Arrays.asList(new Object[][] {
	/////////////////  0   ///////////////////	
		            {
		            "int g(){}"                                                            +"\n"+
		            "int f() interrupt 1 using 1"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "int i=a+3;"                                                           +"\n"+
		            ""                                                                     +"\n"+
		            "g();"                                                                 +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "RC"
		            ,
		            },
    /////////////////  1   ///////////////////	
		            {
		            "int g(){}"                                                            +"\n"+
		            "int f() interrupt 1 using 50"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "int i=a+3;"                                                           +"\n"+
		            "#pragma NOAREGS"                                                      +"\n"+
		            "g();"                                                                 +"\n"+
		            "#pragma AREGS"                                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  2   ///////////////////	
		            {
		            "int g(){}"                                                            +"\n"+
		            "int f() interrupt 1 using 0"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "int i=a+3;"                                                           +"\n"+
		            "g();"                                                                 +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  3   ///////////////////	
		            {
		            "int g(){}"                                                            +"\n"+
		            "int f() interrupt 1 using 0"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "int i=a+3;"                                                           +"\n"+
		            "#pragma NOAREGS"                                                      +"\n"+
		            "g();"                                                                 +"\n"+
		            "#pragma AREGS"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  4   ///////////////////	
		            {
		            "int g(){}"                                                            +"\n"+
		            "int f()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "int i=a+3;"                                                           +"\n"+
		            "g();"                                                                 +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "OK"
		            ,
		            },


				 
				 
		 });
	 }
}
