package softtest.test.keilc.rules.fault;

import static org.junit.Assert.fail;
import static org.junit.Assert.assertEquals;

import java.io.ByteArrayInputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
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

import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.CCharStream;
import softtest.ast.c.CParser;
import softtest.ast.c.ParseException;
import softtest.cfg.c.ControlFlowVisitor;
import softtest.domain.c.analysis.ControlFlowDomainVisitor;
import softtest.config.c.Config;
import softtest.fsm.c.FSMLoader;
import softtest.fsm.c.FSMMachine;
import softtest.fsmanalysis.c.FSMAnalysisVisitor;
import softtest.fsmanalysis.c.FSMControlFlowData;
import softtest.fsmanalysis.c.Report;
import softtest.symboltable.c.OccurrenceAndExpressionTypeFinder;
import softtest.symboltable.c.ScopeAndDeclarationFinder;

@RunWith(Parameterized.class)
public class Test_UVF {
	private String source = null;
	private String compiletype=null;
	private String result = null;
	private static final String fsmPath="softtest/rules/keilc/fault/UVF-0.1.xml";
	FSMAnalysisVisitor fsmAnalysis; 
	private FSMControlFlowData cfData;
	
	public Test_UVF(String source,String compiletype, String result)
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
		           // "	int j = 2;"                                                          +"\n"+
		            "	call(i);  //DEFECT, UVF, i"                                          +"\n"+
		           // "	call(j); //FP "                                                      +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "UVF"
		            ,
		            },
	
////////////////	/  1   chh///////////////////	
		             {
		            "void f3()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	int j;"                                                              +"\n"+
		            "	int m;"                                                              +"\n"+
		            "	m += 1; //DEFECT, UVF, m"                                            +"\n"+
		            "	j++; //DEFECT, UVF, j"                                               +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "UVF"
		            ,
		            },
////////////////	/  2   chh///////////////////	
		            {
		            "void f4() {"                                                          +"\n"+
		            "  int k;"                                                             +"\n"+
		            "  int a = 2;"                                                         +"\n"+
		            "  a = k;   //DEFECT, UVF, k"                                          +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "UVF"
		            ,
		            },
////////////////	/  3  chh ///////////////////	
		            {
		            "void f5()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	int a;"                                                              +"\n"+
		            "	int b;"                                                              +"\n"+
		            "	b = a; //DEFECT, UVF, a"                                             +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "UVF"
		            ,
		            },
////////////////	/  4  chh   普通函数初始化///////////////////	
		             {
		            "int getValue(int);"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "int f7()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "    int	c;"                                                           +"\n"+
		            "    return (c = getValue(0)) == 1 ? 1 : getValue(c); //FP"            +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "OK"
		            ,
		            },
////////////////	/  5   chh  input(int*)函数初始化///////////////////	
		            {
		            "void input(int*);"                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int f10()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	int ii;"                                                             +"\n"+
		            "	input(&ii); //FP"                                                    +"\n"+
		            "	return ii;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "OK"
		            ,
		            },



	/////////////////  6   chh  sscanf函数初始化///////////////////	
	
		            {
		            "void fun()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "	char c[],d[];"                                                         +"\n"+
		                                                               
		            "	sscanf(\"123456\",\"%s\",c);//FP"                                            +"\n"+
		            "	d=c;;"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            
		            "OK"
		            ,
		            },
	/////////////////  7  chh strcpy初始化 ///////////////////	
		             {
		            "void fun()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "char st1[],st2[]=\"aaaaa\";"                                                  +"\n"+
		            "strcpy(st1,st2);"                                                    +"\n"+
		            "}" 
		            ,
		            "keil"
		            ,
		            
		            "OK"
		            ,
		            },
/////////////////  8  chh strcpy初始化不合法 ///////////////////	
		             {
		            "void fun()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "char st1[];"                                                  +"\n"+
		            "strcpy(st1,st1);"                                                    +"\n"+
		            "}" 
		            ,
		            "keil"
		            ,
		            
		            "UVF"
		            ,
		            },
	/////////////////  9  chh strcpy初始化不合法 ///////////////////	
				  {
		            "void fun()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "char str2[],str1[];"                                                  +"\n"+
		            "strcpy(str1,str2);"                                                    +"\n"+
		            "}" 
		            ,
		            "keil"
		            ,
		            
		            "UVF"
		            ,
		            },
/////////////////  10   chh  f(int *i)函数初始化///////////////////	
		             {
		            "void f(int *i);"                                                 +"\n"+
		            "void fun()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "	int a[],c[];"                                                    +"\n"+
		            "	f(a);"                                                    +"\n"+
		            "	c=a;"                                                             +"\n"+
		            "}" 
		            ,
		            "keil"
		            ,
		            "OK"
		            ,
		            },

	/////////////////  11  chh  i=i+1///////////////////	
		            {
		            "fun()"                                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "	int i;"                                                         +"\n"+
		            "	i=i+1;//DEFECT, UVF, i"                                                              +"\n"+
		            "}"
		            ,
		            "keil"
		            ,
		            "UVF"
		            ,
		            },
	/////////////////  12  chh  指针初始化///////////////////	
		
		            {
		            "fun()"                                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "int a[],*p;//FP"                                                        +"\n"+
		            "p=a;"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  13  chh  指针初始化///////////////////	
		    		
		            {
		            "fun()"                                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "	int a[],b[];"                                                        +"\n"+
		            "	int b=a;//FP,a,b作为指针处理"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "OK"
		            ,
		            },
	
/////////////////  14   chh 数组初始化不合法///////////////////	
		    		
		            {
		            "fun()"                                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "	int a[];"                                                        +"\n"+
		            "	a[0]=a[1];"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "UVF"
		            ,
		            },
/////////////////  15   chh  数组初始化///////////////////	
		    		
		            {
		            "fun()"                                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "	int a[];"                                                        +"\n"+
		            "	a[0]=a[1]=0;"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  16   chh sizeof(i)不算对i的非法使用///////////////////	
		              {
		            "int fun()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	int i;"                                                              +"\n"+
		            "	"                                                                    +"\n"+
		            "	return sizeof(i);"                                                   +"\n"+
		            "}"  
		            ,
		            "keil"		           
		            ,
		            "OK"
		            ,
		            },

/////////////////  17  chh strcpy初始化 ///////////////////	
		            {
		            "void fun()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "char st1[],st2[];"                                                  +"\n"+
		            "strcmp(st1,st2);"                                                    +"\n"+
		            "}" 
		            ,
		            "keil"
		            ,
		            
		            "UVF"
		            ,
		            },
	/////////////////  18  chh strcpy初始化 ///////////////////	
		             {
		            "void fun()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "int i;"                                                  +"\n"+
		            "i&=0x03;"                                                    +"\n"+
		            "}" 
		            ,
		            "keil"
		            ,
		            
		            "OK"
		            ,
		            },         
/////////////////  19  chh  for_out///////////////////	//
				     {
			            " fun()"                                                            +"\n"+
			            "{"                                                                    +"\n"+
			            "	int i,k;"                                                              +"\n"+
			            "	for(i=0;i>5;i++)"                                                    +"\n"+
			            "	{"                                                                   +"\n"+
			            "		//k=i;"                                                             +"\n"+
			            "	}"                                                                   +"\n"+
			            "	k=5;"                                                           +"\n"+
			            "}"                                                                    
			            ,
			            "keil"		           
			            ,
			            "OK"
			            ,
			            }, 
/////////////////  20  chh while_head///////////////////	
			             {
			            "void  f()"                                                            +"\n"+
			            "{"                                                                    +"\n"+
			            "int a,b=0;"                                                             +"\n"+
			            "while(b<5)"                                                           +"\n"+
			            "{"                                                                    +"\n"+
			            "b++;"                                                                 +"\n"+
			            "}"                                                                    +"\n"+
			            "a=b;}"                                                                    
			            ,
			            "all"
			            ,
			            "OK"
			            ,
			            },
/////////////////  21  chh   do_while_head///////////////////	
						  {
					            ""                                                                     +"\n"+
					            "void fun()"                                                            +"\n"+
					            "{"                                                                    +"\n"+
					            "	int i,k;"                                                          +"\n"+
					            "	k=0;"                                                          +"\n"+
					            "	do{"                                                                 +"\n"+
					            "	    i=k;"                                                                 +"\n"+
					            "		"                                                               +"\n"+
					            "		k++;"                                                               +"\n"+
					            "		}while(i<10);"                                                       +"\n"+
					            "		i++;"                                                               +"\n"+
					            "}"
					            ,
					            "keil"
					            ,
					            "OK"
					            ,
					            },
		

/////////////////  22   chh   for不可达初始化///////////////////	////
			            {
				            
				            "int fun()"                                                            +"\n"+
				            "{"                                                                    +"\n"+
				            "	int i,k,j;"                                                            +"\n"+
				            "	for(i=12;i<10;i++)//条件不符合，不会进入for循环，k没有初始化，但是结果OK"                                                    +"\n"+
				            "	{"                                                                   +"\n"+
				            "		//break;"                                                                   +"\n"+
				            "		k=i;"                                                                   +"\n"+
				            "	}"                                                               +"\n"+
				            "	j=k;"                                                                   +"\n"+
				            "}"
				            ,
				            "keil"
				            ,
				            "UVF"
				            ,
				            },

/////////////////  23  chh if 不可达初始化///////////////////	
				             {
				            "void fun()"                                                           +"\n"+
				            "{"                                                                    +"\n"+
				            "	int i=1,x,n;"                                                        +"\n"+
				            "	if(i==0) scanf(\"%d\",&x);//判断条件不成立，即x未赋值，依旧OK"                                            +"\n"+
				            "	n=x;"                                                                +"\n"+
				            "}" 
				            ,
				            "keil"
				            ,
				            
				            "UVF"
				            ,
				            },
/////////////////  24 chh switch初始化不可达   ///////////////////	
				            {//
				            "void fun()"                                                           +"\n"+
				            "{"                                                                    +"\n"+
				            "int i,a,b;"                                                         +"\n"+
				            "i=0;"                                                                   +"\n"+
				            "switch(i)"                                                            +"\n"+
				            "{"                                                                    +"\n"+
				            "case 1:a=2;break;"                                                    +"\n"+
				            "default:break;"                                                       +"\n"+
				            "}"                                                                    +"\n"+
				            "b=a;"                                                                 +"\n"+
				            "}"                                                                    
				            ,
				            "keil"
				            ,
				            "OK"
				            ,
				            },
/////////////////  25 chh  if初始化不可达  ///////////////////	
	
						             {
						            "void  f()"                                                            +"\n"+
						            "{"                                                                    +"\n"+
						            "int j,y,x;"                                                             +"\n"+
						            "x=1;"                                                                 +"\n"+
						            "y=x+1;"                                                               +"\n"+
						            "if(x>y)"                                                              +"\n"+
						            "{"                                                                    +"\n"+
						            "j=5;"                                                                 +"\n"+
						            "}"                                                                    +"\n"+
						            "x=j;"                                                                 +"\n"+
						            "}"                                                                    
						            ,
						            "keil"
						            ,
						            "UVF"
						            ,
						            },
	
	/////////////////  26 chh do_while 内先使用后初始化   ///////////////////	
		            {
		            "f()"                                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "char a;"                                                              +"\n"+
		            "do{a++;a=0;}while(1);"                                                      +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "UVF"
		            ,
		            },
	/////////////////  27 chh while 内先使用后初始化   ///////////////////	
		            {
		            "f()"                                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "char a;"                                                              +"\n"+
		            "while(1){a++;a=0;}"                                                      +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "UVF"
		            ,
		            },
	/////////////////  28 chh for 内先使用后初始化   ///////////////////	
		            {
		            "f()"                                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "char a;"                                                              +"\n"+
		            "for(;;){a++;a=0;}"                                                      +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "UVF"
		            ,
		            },
	/////////////////  29 chh if 内先使用后初始化   ///////////////////	
		            {
		            "f()"                                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "char a;"                                                              +"\n"+
		            "if(1){a++;a=0;}"                                                      +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "UVF"
		            ,
		            },
	
		 });
	 }
}


