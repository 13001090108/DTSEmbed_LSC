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

@RunWith(Parameterized.class)
public class Test_NUAV {
	private String source = null;
	private String compiletype=null;
	private String result = null;
	private static final String fsmPath="softtest/rules/keilc/fault/NUAV-0.1.xml";
	FSMAnalysisVisitor fsmAnalysis; 
	private FSMControlFlowData cfData;
	
	public Test_NUAV(String source,String compiletype, String result)
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
		
		astroot.jjtAccept(new ControlFlowVisitor(), null);
		
		astroot.jjtAccept(new DUAnalysisVisitor(), null);
		
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

		            "void call(int);"                                                      +"\n"+
		            ""                                                                     +"\n"+
		            "void f1()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	int i;"                                                              +"\n"+
		            "	i = 2; //DEFECT, DANU, i"                                            +"\n"+
		            "	i = 3;"                                                              +"\n"+
		            "	call(i);"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "NUAV"
		            ,
		            },
////////////////	/  1   ///////////////////	
		            {
		            "void call(int);"                                                      +"\n"+
		            ""                                                                     +"\n"+
		            "void f2(int a)"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "	int i;"                                                              +"\n"+
		            "	i = 2; //FP"                                                         +"\n"+
		            "	if(a > 0)"                                                           +"\n"+
		            "		i = 4;"                                                             +"\n"+
		            "	call(i);"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "NUAV"
		            ,
		            },
////////////////	/  2   ///////////////////	
		            {
		            "void f3(int a)"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "	int i;"                                                              +"\n"+
		            "	i = 3;"                                                              +"\n"+
		            "	while(a > 0)"                                                        +"\n"+
		            "	{"                                                                   +"\n"+
		            "		if(i>0)"                                                            +"\n"+
		            "			i = i + 1; //FP"                                                   +"\n"+
		            "		if(a > 2)"                                                          +"\n"+
		            "			a--;"                                                              +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OK"
		            ,
		            },
////////////////	/  3   ///////////////////	
		            {
		            "void f4(int a)"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "	int j;"                                                              +"\n"+
		            "	while(a > 0) {"                                                      +"\n"+
		            "		j = 3; //DEFECT"                                                    +"\n"+
		            "		j = 4;"                                                             +"\n"+
		            "		call(j);"                                                           +"\n"+
		            "		a--;"                                                               +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "NUAV"
		            ,
		            },
////////////////	/  4   ///////////////////	
		            {
		            "int f5()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "	int k;"                                                              +"\n"+
		            "	k = 2; //FP"                                                         +"\n"+
		            "	++k;"                                                                +"\n"+
		            "	return k;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  5   ///////////////////	
		            {
		            "int g(){return 1;}"                                                   +"\n"+
		            "int f(){"                                                             +"\n"+
		            "int i;"                                                               +"\n"+
		            "i=g();"                                                               +"\n"+
		            "return i;"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  6   ///////////////////	
		            {
		            "int f(){return 0;}"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "int g(){"                                                             +"\n"+
		            "int i;"                                                               +"\n"+
		            "i=f();"                                                               +"\n"+
		            "for(;i<10;i++){"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    +"\n"+
		            "return i;"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OK"
		            ,
		            },


/////////////////  7  chh ///////////////////	
		            {
		            "int f5(int a)"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	int i=j=1;"                                                              +"\n"+
		            "	if((j=get())==0) return i;//FP"                                            +"\n"+
		            "}	"                                                                   
		            ,
		            "keil"
		            ,
		            "OK"
		            ,
		            },
/////////////////  8  chh ///////////////////	
		            {
		            "int f6(int a)"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	int i;"                                                              +"\n"+
		            "	i=1;"                                                              +"\n"+
		            "	if((i=get())>0) return i;//FP"                                            +"\n"+
		            "}	"                                                                   
		            ,
		            "keil"
		            ,
		            "NUAV"
		            ,
		            },
////////////////	/  9  chh ///////////////////	
		            {
		            "void f1()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	int j, i;"                                                           +"\n"+
		            "	j = i = 3; //DEFECT, j"                                              +"\n"+
		            "   j=i=4;"                                                               +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "NUAV"
		            ,
		            },

	/////////////////  10   chh ///////////////////	
		            {
		            "main()"                                                               +"\n"+
		            "{"                                                                    +"\n"+
		            "	unsigned char j,a,b,c,d,e, flag;"                                    +"\n"+
		            "	SPI_Init();					    //SPI initialization"                            +"\n"+
		            "	timer0_init ();"                                                     +"\n"+
		            "	PSD_reg.VM|=0x80;				//enable PSD peripheral IO"                     +"\n"+
		            "    lcd_init();"                                                      +"\n"+
		            "	for (j =0x30; j<0x30; j += 4)"                                       +"\n"+
		            "	{"                                                                   +"\n"+
		            "		flag = 0;"                                                          +"\n"+
		            "		a=b=c=d=e=0;"                                                       +"\n"+
		            "		SPICLKD = j;"                                                       +"\n"+
		            "        lcd_clear();"                                                 +"\n"+
		            "		printfLCD(\"SPICLKD=0x%x\\n\",j);"                                     +"\n"+
		            "//------------------ erase  serial flash M25P80-----------------------------------"+"\n"+
		            "	a = SPI_transfer(W_ENABLE,R_buf,1); //enable write command"          +"\n"+
		            "	d = SPI_transfer(ERASE,R_buf,4); //erase command"                    +"\n"+
		            " 		TR0=1;delay_1sec( ); delay_1sec( ); TR0=0;// wait for erase end, 1 sec is too short"+"\n"+
		            ""                                                                     +"\n"+
		            "//------------------ write  serial flash M25P80-----------------------------------																		//2 sec is enough "+"\n"+
		            "	c = SPI_transfer(W_ENABLE,R_buf,1); //enable write command"          +"\n"+
		            "	d = SPI_transfer(WRITE,R_buf,36);  //write 32 bytes to serial flash" +"\n"+
		            "		TR0=1;delay_10ms();delay_10ms();TR0=0;	//wait for write end	"       +"\n"+
		            ""                                                                     +"\n"+
		            "//------------------ read  serial flash M25P80-----------------------------------	"+"\n"+
		            "	e = SPI_transfer(READ,R_buf,36);  //read 32 bytes from serial flash" +"\n"+
		            ""                                                                     +"\n"+
		            "	printfLCD(\"T:%x R:%x ROR:%x\\n\",tlen,rlen,e);"                        +"\n"+
		            "		TR0=1;delay_1sec( );TR0=0;"                                         +"\n"+
		            "	}"                                                                   +"\n"+
		            "	while(1);"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "NUAV"
		            ,
		            },
	/////////////////  11 chh  ///////////////////	
		            {
		            "void f()"                                                             +"\n"+
		            "{	"                                                                   +"\n"+
		            "	int i,a,b,c;"                                                         +"\n"+
		            "	for(i=0;i<0;i++)"                                                    +"\n"+
		            "	{"                                                                   +"\n"+
		            "		a=b=c=5;"                                                           +"\n"+
		            //"		a=3;"                                                               +"\n"+
		            "		b=5;"                                                               +"\n"+
		           // "		c=3;"                                                               +"\n"+
		           // "		b=5;"                                                               +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "NUAV"
		            ,
		            },


////////////////	/  12  chh ///////////////////	
		            {
		            "f(){"                                                                 +"\n"+

		            "int i,j;"                                                            +"\n"+
		            "i=10;"                                                            +"\n"+
		            "j=10;"                                                            +"\n"+		           
		            "i=i+5;"                                                               +"\n"+
		            "i=j+3;"                                                               +"\n"+

		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "NUAV"
		            ,
		            },
////////////////	/  13 chh   ///////////////////	
		            {
		            "void call(int);"                                                      +"\n"+
		            ""                                                                     +"\n"+
		            "void f1()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	int i=2;"                                                              +"\n"+
		            "	i = 3;"                                                              +"\n"+
		            "	call(i);"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "NUAV"
		            ,
		            },

////////////////	/  14  chh ///////////////////	

		            {
		            "f(){"                                                             +"\n"+
		            "int i=10,j;"                                                            +"\n"+		           
		            "i=5;"                                                               +"\n"+
		            "j=i*3;"                                                               +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "NUAV"
		            ,
		            },
////////////////	/  15  chh ///////////////////	

		           {
		            "f(){"                                                             +"\n"+
		            "int i=10,j;"                                                            +"\n"+
		            "j=i+3;"                                                            +"\n"+
		            "i=i%5;"                                                               +"\n"+
		            "i%=10;"                                                               +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "NUAV"
		            ,
		            },
	/////////////////  16 chh if   ///////////////////	
		            {
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "int i=1,a;"                                                           +"\n"+
		            "if(i==0)a=1;"                                                         +"\n"+
		            "if(i==1)a=2;"                                                         +"\n"+
		            "if(i==2)a=3;"                                                         +"\n"+
		            "if(i==3)a=4;"                                                         +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "NUAV"
		            ,
		            },
	/////////////////  17 chh if   ///////////////////	
		            {
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "int i=1,b=1;"                                                         +"\n"+
		            "if(i==0)b=1;"                                                         +"\n"+
		            "if(i==1)b=2;"                                                         +"\n"+
		            "if(i==2)b=3;"                                                         +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "NUAV"
		            ,
		            },
	/////////////////  18 chh if   ///////////////////	
		            {
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "int i=1,c=1;"                                                         +"\n"+
		            "if(i==0)"                                                             +"\n"+
		            "c=1;"                                                                 +"\n"+
		            "if(i==1)"                                                             +"\n"+
		            "c=2;"                                                                 +"\n"+
		            "if(i==2)"                                                             +"\n"+
		            "c=3;"                                                                 +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "NUAV"
		            ,
		            },

	/////////////////  19 chh if_else   ///////////////////	
		            {
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "int a=1,b;"                                                           +"\n"+
		            "if(a==1)b=1;"                                                         +"\n"+
		            "else b=2;"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  20 chh switch    ///////////////////	
		            {
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "int a=1,b;"                                                           +"\n"+
		            "switch(a)"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "case 1:b=1;break;"                                                    +"\n"+
		            "case 2:b=2;break;"                                                    +"\n"+
		            "default:break;"                                                       +"\n"+
		            "}"                                                                    +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  21 chh goto   ///////////////////	
		            {
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "int a,b,c,i=1;"                                                       +"\n"+
		            "goto ac;"                                                             +"\n"+
		            "bc:"                                                                  +"\n"+
		            "i=2;"                                                                 +"\n"+
		            "ac:"                                                                  +"\n"+
		            "a=i;"                                                                 +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  22 chh goto   ///////////////////	
		            {
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "int a,b,c,i=1;"                                                       +"\n"+
		            "goto ac;"                                                             +"\n"+
		            "bc:"                                                                  +"\n"+
		            "i=2;"                                                                 +"\n"+
		            "ac:"                                                                  +"\n"+
		            "a=i;"                                                                 +"\n"+
		            "goto bc;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  23 chh goto   ///////////////////	
		            {
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "int a,b,c,i=1;"                                                       +"\n"+
		            "goto ac;"                                                             +"\n"+
		            "bc:"                                                                  +"\n"+
		            "i=2;"                                                                 +"\n"+
		            "goto d;"                                                              +"\n"+
		            "ac:"                                                                  +"\n"+
		            "a=i;"                                                                 +"\n"+
		            "goto bc;"                                                             +"\n"+
		            "d:"                                                                   +"\n"+
		            ";"                                                                    +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OK"
		            ,
		            },
/////////////////  0   ///////////////////	
		            {
		            "int CC6_uwGetChannelRegister()"                             +"\n"+
		            "{"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "  int ChName=1,Value ,a;"                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "  SFR_PAGE(_cc1, SST2);          // switch to page 1"                 +"\n"+
		            ""                                                                     +"\n"+
		            "  if ( ChName == 0)                             //  if Channel_0"     +"\n"+
		            "    Value = 1;    //  Capture/Compare Register for Channel CC60"+"\n"+
		            ""                                                                     +"\n"+
		            "  if ( ChName == 1)                             //  if Channel_1"     +"\n"+
		            "    Value = 2;    //  Capture/Compare Register for Channel CC61"+"\n"+
		            ""                                                                     +"\n"+
		            "  if ( ChName == 2)                             //  if Channel_2"     +"\n"+
		            "    Value = 2;     // Capture/Compare Register for Channel CC62"+"\n"+
		            ""                                                                     +"\n"+
		            "  if ( ChName == 3)                           //  if Channel_3"     +"\n"+
		            "    Value = 3;    //  Capture/Compare Register for Channel CC63"+"\n"+
		            "//a=Value;Value=4;"                                                                     +"\n"+
		            " // SFR_PAGE(_cc0, RST2);          // restore the old CCU page"         +"\n"+
		            ""                                                                     +"\n"+
		            "  return (Value);"                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "NUAV"
		            ,
		            },
		 });
	 }
}

