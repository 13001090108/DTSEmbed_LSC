package softtest.test.keilc.rules.fault;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.io.ByteArrayInputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import org.apache.log4j.BasicConfigurator;
import org.apache.log4j.PropertyConfigurator;
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
import softtest.domain.c.analysis.ControlFlowDomainVisitor;
import softtest.fsm.c.FSMLoader;
import softtest.fsm.c.FSMMachine;
import softtest.fsmanalysis.c.FSMAnalysisVisitor;
import softtest.fsmanalysis.c.FSMControlFlowData;
import softtest.fsmanalysis.c.Report;
import softtest.symboltable.c.OccurrenceAndExpressionTypeFinder;
import softtest.symboltable.c.ScopeAndDeclarationFinder;

@RunWith(Parameterized.class)
public class Test_DOF {
	private String source = null;
	private String compiletype=null;
	private String result = null;
	private static final String fsmPath="softtest/rules/keilc/fault/DOF-0.1.xml";
	private FSMAnalysisVisitor fsmAnalysis; 
	private FSMControlFlowData cfData;
	
	public Test_DOF(String source,String compiletype, String result)
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
	
	private void analysis(ASTTranslationUnit astroot){
		astroot.jjtAccept(new ScopeAndDeclarationFinder(), null);
		astroot.jjtAccept(new OccurrenceAndExpressionTypeFinder(), null);
		astroot.jjtAccept(new ControlFlowVisitor(), null);
		astroot.jjtAccept(new ControlFlowDomainVisitor(), null);
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
		cfData = new FSMControlFlowData();
		List<Report> reports = new ArrayList<Report>();
		cfData.setReports(reports);
		fsmAnalysis=new FSMAnalysisVisitor(cfData); 
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
		            "fff(){"                                                               +"\n"+
		            "char i=126;"                                                   +"\n"+
		            "	i++;"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  1   ///////////////////	
		            {
		            "fff(){"                                                               +"\n"+
		            "char i=127;"                                                   +"\n"+
		            "	i++;"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "DOF"
		            ,
		            },		            
	/////////////////  2   ///////////////////	
		            {
		            "fff(){"                                                               +"\n"+
		            "int i=32766;"                                                   +"\n"+
		            "	i++;"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  3   ///////////////////	
		            {
		            "fff(){"                                                               +"\n"+
		            "int i=32767;"                                                   +"\n"+
		            "	i++;"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "DOF"
		            ,
		            },
	/////////////////  4   ///////////////////	
		            {
		            "fff(){"                                                               +"\n"+
		            "short i=32767;"                                                   +"\n"+
		            "	i++;"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "DOF"
		            ,
		            },		            
	/////////////////  5   ///////////////////	
		            {
		            "fff(){"                                                               +"\n"+
		            "short i=32766;"                                                   +"\n"+
		            "	i++;"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "OK"
		            ,
		            },				 
	/////////////////  6   ///////////////////	
		            {
		            "fff(){"                                                               +"\n"+
		            "unsigned short i=65534;"                                                   +"\n"+
		            "	i++;"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "OK"
		            ,
		            },	
	/////////////////  7   ///////////////////	
		            {
		            "fff(){"                                                               +"\n"+
		            "unsigned short i=65535;"                                                   +"\n"+
		            "	i++;"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "DOF"
		            ,
		            },	
	/////////////////  8   ///////////////////	
		            {
		            "fff(){"                                                               +"\n"+
		            "unsigned char i=254;"                                                   +"\n"+
		            "	i++;"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "OK"
		            ,
		            },	
	/////////////////  9   ///////////////////	
		            {
		            "fff(){"                                                               +"\n"+
		            "unsigned char i=255;"                                                   +"\n"+
		            "	i++;"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "DOF"
		            ,
		            },	
	/////////////////  10   ///////////////////	
		            {
		            "fff(){"                                                               +"\n"+
		            "unsigned int i=65534;"                                                   +"\n"+
		            "	i++;"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  11   ///////////////////	
		            {
		            "fff(){"                                                               +"\n"+
		            "unsigned int i=65535;"                                                   +"\n"+
		            "	i++;"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "DOF"
		            ,
		            },
	/////////////////  12   ///////////////////	
		            {
		            "f(){"                                                                 +"\n"+
		            "unsigned char i;"                                                             +"\n"+
		            "if(i<256)"                                                              +"\n"+
		            "	return i;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "DOF"
		            ,
		            },
	/////////////////  13   ///////////////////	
		            {
		            "f(){"                                                                 +"\n"+
		            "unsigned char i;"                                                             +"\n"+
		            "if(i<255)"                                                              +"\n"+
		            "	return i;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  14   ///////////////////	
		            {
		            "f(){"                                                                 +"\n"+
		            "unsigned char i,j;"                                                             +"\n"+
		            "if(i<j)"                                                              +"\n"+
		            "	return i;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  15   ///////////////////	
		            {
		            "f(){"                                                                 +"\n"+
		            "unsigned char i;"                                                             +"\n"+
		            "short j=300;"                                                             +"\n"+
		            "if(i<j)"                                                              +"\n"+
		            "	return i;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "DOF"
		            ,
		            },
	/////////////////  16   ///////////////////	
		            {
		            "sfr SP=0xFF;"                                                         
		            ,
		            "keil"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  17   ///////////////////	
		            {
	            	 "f(){"                                                               +"\n"+
			            "sfr SP=0x200;//[0、511]"                                                  +"\n"+
			            "}"                                                                    
			            ,
			          "keil"
			          ,
			          "DOF"
			          ,		        
			            },

	/////////////////  18  liuli ///////////////////	
		            {
	            	 "f(){"                                                               +"\n"+
			            "sfr16 SP=0x10000;"                                                   +"\n"+
			            "}"                                                                    
			            ,
			          "keil"
			          ,
			          "DOF"
			          ,		        
		            },
	/////////////////  19 chh   ///////////////////	
		            {
		            "int call()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "char a=5,b=100;"                                                      +"\n"+
		            "a=a*b;"                                                               +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "DOF"
		            ,
		            },

/////////////////  20 chh   ///////////////////	
		            {
		            "void p()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "    char i=50;"                                                       +"\n"+
		            "    printf(\"%c\",i*1000+50);"                                               +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "DOF"
		            ,
		            },
		 });
	 }
}
