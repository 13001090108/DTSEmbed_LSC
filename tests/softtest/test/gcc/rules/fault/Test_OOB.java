package softtest.test.gcc.rules.fault;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

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
import softtest.ast.c.ASTFunctionDefinition;
import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.CCharStream;
import softtest.ast.c.CParser;
import softtest.ast.c.ParseException;
import softtest.ast.c.SimpleNode;
import softtest.callgraph.c.CGraph;
import softtest.callgraph.c.CVexNode;
import softtest.cfg.c.ControlFlowData;
import softtest.cfg.c.ControlFlowVisitor;
import softtest.config.c.Config;
import softtest.domain.c.analysis.ControlFlowDomainVisitor;
import softtest.fsm.c.FSMLoader;
import softtest.fsm.c.FSMMachine;
import softtest.fsmanalysis.c.FSMAnalysisVisitor;
import softtest.fsmanalysis.c.FSMControlFlowData;
import softtest.fsmanalysis.c.Report;
import softtest.interpro.c.InterCallGraph;
import softtest.interpro.c.InterMethodVisitor;
import softtest.symboltable.c.AbstractScope;
import softtest.symboltable.c.OccurrenceAndExpressionTypeFinder;
import softtest.symboltable.c.ScopeAndDeclarationFinder;

@RunWith(Parameterized.class)
public class Test_OOB {
	private String source = null;
	private String compiletype=null;
	private String result = null;
	private static final String fsmPath="softtest/rules/gcc/fault/OOB-0.1.xml";
	FSMAnalysisVisitor fsmAnalysis; 
	private FSMControlFlowData cfData;
	
	public Test_OOB(String source,String compiletype, String result)
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
		
		//清空原有全局分析中产生的函数摘要信息
		InterCallGraph.getInstance().clear();
		astroot.jjtAccept(new InterMethodVisitor(), null);
		
		CGraph g = new CGraph();
		((AbstractScope)(astroot.getScope())).resolveCallRelation(g);
		List<CVexNode> list = g.getTopologicalOrderList();
		Collections.reverse(list);
		
		ControlFlowData flow = new ControlFlowData();
		ControlFlowVisitor cfv = new ControlFlowVisitor();
		ControlFlowDomainVisitor cfd = new ControlFlowDomainVisitor();
		
		for (CVexNode cvnode : list) {
			SimpleNode node = cvnode.getMethodNameDeclaration().getNode();
			if (node instanceof ASTFunctionDefinition) {
				cfv.visit((ASTFunctionDefinition)node, flow);
				cfd.visit((ASTFunctionDefinition)node, null);
			} 
		}
		
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
////////////////////0   ///////////////////	
				 {
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "  int a[5] ;"                                            +"\n"+
		            "  a[6] = 1;  //DEFECT,OOB,a"                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB"
		            ,
		            }, 
////////////////////  1   ///////////////////	
		            {
		            "int f()"                                                              +"\n"+
		            "{"                                                                    +"\n"+
		            "  static   char buf[10] = \"\";"                                        +"\n"+
		            "  buf[9] = 'A';   //FP,OOB"                                           +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OK"
		            ,
		            },
 
////////////////////  2   ///////////////////	
		            {
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "  int a[5] ;"                                             +"\n"+
		            "  a[5] = 1;  //DEFECT,OOB,a"                                          +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OOB"
		            ,
		            },
////////////////////  3   ///////////////////	
		            {
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "  int a[5] ;"                                             +"\n"+
		            "  a[4] = 1;  //FP,OOB"                                          +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OK"
		            ,
		            },		            
////////////////	/  4   ///////////////////	
		            {
		            "int c[5];"                                                            +"\n"+
		            "void f () {"                                                          +"\n"+
		            "  int b[5];"                                                          +"\n"+
		            "  b[4]; //FP,OOB"                                               +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OK"
		            ,
		            },
////////////////	/  5   ///////////////////	
		            {
		            "int c[5];"                                                            +"\n"+
		            "void f () {"                                                          +"\n"+
		            "  int b[5];"                                                          +"\n"+
		            "  b[6]; //DEFECT,OOB,b"                                               +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OOB"
		            ,
		            },		            
////////////////	/  6   ///////////////////	
		            {
		            "int c[5];"                                                            +"\n"+
		            "void f () {"                                                          +"\n"+
		            "  c[6];  //DEFECT,OOB,c"                                              +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OOB"
		            ,
		            },
////////////////	/  7   ///////////////////	
		            {
		            "int c[7];"                                                            +"\n"+
		            "void f () {"                                                          +"\n"+
		            "  c[6];  //FP,OOB"                                              +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OK"
		            ,
		            },       
////////////////	/  8   ///////////////////	
		            {
		            "int c[5];"                                                +"\n"+
		            "void f () {"                                                          +"\n"+
		            "  c[4];  //FP,OOB"                                              +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OK"
		            ,
		            },	      
////////////////	/  9   ///////////////////	
		            {
		            "int c[5];"                                                +"\n"+
		            "void f () {"                                                          +"\n"+
		            "  c[5];  //DEFECT,OOB,c"                                              +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OOB"
		            ,
		            },	     
////////////////	/  10   ///////////////////	
//这种情况本来可以测试，但是由于测工程的时候区间运算会不准确引起大量误报，所以暂时放弃此功能		            
		            {
		            "struct str{"                                                          +"\n"+
		            "	char*s;"                                                             +"\n"+
		            "	char a[100];"                                                        +"\n"+
		            "};"                                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void test5(int i){"                                                   +"\n"+
		            "      int a[120];"                                                    +"\n"+
		            "	  struct str s;"                                                     +"\n"+
		            "      a[110]=1;//FP,OOB"                                              +"\n"+
		            "	  if(i<=100){"                                                       +"\n"+
		            "		  s.a[i]=1;//DEFECT,OOB,a"                                          +"\n"+
		            "	  }"                                                                 +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OOB"
		            ,
		            },
////////////////	/  11   ///////////////////	
//这种情况本来可以测试，但是由于测工程的时候区间运算会不准确引起大量误报，所以暂时放弃此功能	
		            {
		            "struct str{"                                                          +"\n"+
		            "	char*s;"                                                             +"\n"+
		            "	char a[100];"                                                        +"\n"+
		            "};"                                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void test5(int i){"                                                   +"\n"+
		            "      int a[120];"                                                    +"\n"+
		            "	  struct str s;"                                                     +"\n"+
		            "      a[110]=1;//FP,OOB"                                              +"\n"+
		            "	  if(i<100){"                                                       +"\n"+
		            "		  s.a[i]=1;"                                          +"\n"+
		            "	  }"                                                                 +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OK"
		            ,
		            },
////////////////	/  12   ///////////////////	
		            {
		            "int test1 () {"                                                       +"\n"+
		            "  int a[4] ;"                                                         +"\n"+
		            "  int i = 4;"                                                         +"\n"+
		            "  a[i] = 1;	//DEFECT,OOB,a"                                           +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OOB"
		            ,
		            },     
////////////////	/  13   ///////////////////	
		            {
		            "int test1 () {"                                                       +"\n"+
		            "  int a[4] ;"                                                         +"\n"+
		            "  int i = 3;"                                                         +"\n"+
		            "  a[i] = 1;	//DEFECT,OOB,a"                                           +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OK"
		            ,
		            },  	    
////////////////	/  14   ///////////////////	
//这种情况本来可以测试，但是由于测工程的时候区间运算会不准确引起大量误报，所以暂时放弃此功能
		            {
		            "int test1 () {"                                                       +"\n"+
		            "  int i ;"                                                            +"\n"+
		            "  int a[4] ;"                                              +"\n"+
		            "  if(i > 2)"                                                          +"\n"+
		            "  { "                                                                 +"\n"+
		            "     a[i] = 1; //DEFECT,OOB,a"                                        +"\n"+
		            "  }	"                                                                 +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OOB"
		            ,
		            },
////////////////	/  15   ///////////////////	
//这种情况本来可以测试，但是由于测工程的时候区间运算会不准确引起大量误报，所以暂时放弃此功能			            
		            {
		            "int test3 () {"                                                       +"\n"+
		            "  int i ;"                                                            +"\n"+
		            "  int a[4];"                                              +"\n"+
		            "  if(i > 0 || i < 3)"                                                 +"\n"+
		            "  {"                                                                  +"\n"+
		            "     a[i] = 1; //DEFECT,OOB,a"                                        +"\n"+
		            "  }"                                                                  +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OOB"
		            ,
		            },
////////////////	/  16   ///////////////////	
		            {
		            "int test2 () {"                                                       +"\n"+
		            "  int i ;"                                                            +"\n"+
		            "  int a[4] ;"                                              +"\n"+
		            "  if(i> 0 && i < 3)"                                                  +"\n"+
		            "  {"                                                                  +"\n"+
		            "     a[i] = 1; //FP,OOB"                                              +"\n"+
		            "  }"                                                                  +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OK"
		            ,
		            },	            
////////////////	/  17   ///////////////////	
		            {
		            "int c[3][3];"                                                         +"\n"+
		            "void f(){"                                                            +"\n"+
		            "  int b[3][3];"                                                       +"\n"+
		            "  b[1][1]=0;"                                                         +"\n"+
		            "  b[1][2]=0;"                                                         +"\n"+
		            "  b[3][1]=0;  //DEFECT,OOB,b"                                         +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OOB"
		            ,
		            },
////////////////	/  18   ///////////////////	
		            {
		            "int c[3][3];"                                                         +"\n"+
		            "void f(){"                                                            +"\n"+
		            "  int b[3][3];"                                                       +"\n"+
		            "  b[1][1]=0;"                                                         +"\n"+
		            "  b[1][2]=0;"                                                         +"\n"+
		            "  b[2][2]=0;  //FP,OOB"                                         +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OK"
		            ,
		            },	            
////////////////	/ 19   ///////////////////	
		            {
		            "int c[3][3];"                                                         +"\n"+
		            "void f(){"                                                            +"\n"+
		            "  int b[3][3];"                                                       +"\n"+
		            "  b[1][1]=0;"                                                         +"\n"+
		            "  b[1][2]=0;"                                                         +"\n"+
		            "  b[2][3]=0;  //DEFECT,OOB,b"                                         +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OOB"
		            ,
		            },         
////////////////	/  20   ///////////////////	
		            {
		            "int c[3][3];"                                                         +"\n"+
		            "void f(){"                                                            +"\n"+
		            "  c[1][3]=0;  //DEFECT,OOB,c"                                         +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OOB"
		            ,
		            }, 
////////////////	/  21   ///////////////////	
		            {
		            "int c[3][3];"                                                         +"\n"+
		            "void f(){"                                                            +"\n"+
		            "  c[2][2]=0;  //FP,OOB"                                         +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OK"
		            ,
		            }, 
////////////////	/  22   ///////////////////	
		            {
		            "int c[3][3];"                                                         +"\n"+
		            "void f(){"                                                            +"\n"+
		            "  c[3][1]=0;  //DEFECT,OOB,c"                                         +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OOB"
		            ,
		            }, 	            
////////////////	/  23   ///////////////////	
		            {
		            "void f(){"                                                            +"\n"+
		            "  int b[3][3];"                              +"\n"+
		            "  b[1][1]=0;"                                                         +"\n"+
		            "  b[1][2]=0;"                                                         +"\n"+
		            "  b[3][1]=0; //DEFECT,OOB,b"                                          +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OOB"
		            ,
		            },      
////////////////	/  24   ///////////////////	
		            {
		            "void f(){"                                                            +"\n"+
		            "  int b[3][3];"                              +"\n"+
		            "  b[1][1]=0;"                                                         +"\n"+
		            "  b[1][2]=0;"                                                         +"\n"+
		            "  b[1][3]=0; //DEFECT,OOB,b"                                          +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OOB"
		            ,
		            },              
////////////////	/  25   ///////////////////	
		            {
		            "void f(){"                                                            +"\n"+
		            "  int b[3][3];"                              +"\n"+
		            "  b[1][1]=0;"                                                         +"\n"+
		            "  b[1][2]=0;"                                                         +"\n"+
		            "  b[2][2]=0; //FP,OOB"                                          +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OK"
		            ,
		            },             
////////////////	/  26   ///////////////////	
		            {
		            "void f(){"                                                            +"\n"+
		            "  int b[4][3];"                              +"\n"+
		            "  b[1][1]=0;"                                                         +"\n"+
		            "  b[1][2]=0;"                                                         +"\n"+
		            "  b[3][1]=0; //FP,OOB"                                          +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OK"
		            ,
		            },      
////////////////	/  27   ///////////////////	
		            {
		            "void f(){"                                                            +"\n"+
		            "  int b[3][4];"                              +"\n"+
		            "  b[1][1]=0;"                                                         +"\n"+
		            "  b[1][2]=0;"                                                         +"\n"+
		            "  b[1][3]=0; //FP,OOB"                                          +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OK"
		            ,
		            },    
////////////////	/  28   ///////////////////	
		            {
		            "int func1(int a) {"                                                   +"\n"+
		            "	int array[4];"                                                       +"\n"+
		            "	if (a > 4 || a < 0) {"                                               +"\n"+
		            "		return 0;"                                                          +"\n"+
		            "	}"                                                                   +"\n"+
		            "	array[a] = 1;  //DEFECT,OOB,array"                                   +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OOB"
		            ,
		            },
////////////////	/  29   ///////////////////	
		            {
		            "int func1(int a) {"                                                   +"\n"+
		            "	int array[4];"                                                       +"\n"+
		            "	if (a >= 4 || a < 0) {"                                               +"\n"+
		            "		return 0;"                                                          +"\n"+
		            "	}"                                                                   +"\n"+
		            "	array[a] = 1;  //FP,OOB"                                   +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OK"
		            ,
		            },
////////////////	/  30   ///////////////////	
		            {
		            "int func2(int a) {"                                                   +"\n"+
		            "	int array[4];"                                                       +"\n"+
		            "	if (a>=0 && a<=4) {"                                                 +"\n"+
		            "		array[a] = 1;  //DEFECT,OOB,array"                                  +"\n"+
		            "		"                                                                   +"\n"+
		            "	}"                                                                   +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OOB"
		            ,
		            },	            
////////////////	/  31   ///////////////////	
		            {
		            "int main()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "	int a[10];"                                    +"\n"+
		            "	a[10] = 1;  //DEFECT,OOB,a"                                          +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OOB"
		            ,
		            },
////////////////	/  32   ///////////////////	
		            {
		            "int main()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "	int b[10];"                                                      +"\n"+
		            "	b[10]=0;//DEFECT,OOB,b"                                              +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OOB"
		            ,
		            },
////////////////	/  33   ///////////////////	
		            {
		            "int main()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "	int b[10];"                                                      +"\n"+
		            "	b[9]=0;//FP,OOB"                                              +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OK"
		            ,
		            },
////////////////	/  34   ///////////////////	
		            {
		            "typedef struct _Test {"                                               +"\n"+
		            "	int a[2];"                                                           +"\n"+
		            "} Test;"                                                              +"\n"+
		            ""                                                                     +"\n"+
		            "int test1()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	Test st[2];"                                                   +"\n"+
		            "	st[0].a[0] = 1;"                                                     +"\n"+
		            "	st[0].a[1] = 1;"                                                     +"\n"+
		            "	st[1].a[2] = 1;  //DEFECT,OOB,a"                                    +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OOB"
		            ,
		            },
////////////////	/  35   ///////////////////	
		            {
		            "typedef struct _Test {"                                               +"\n"+
		            "	int a[2];"                                                           +"\n"+
		            "} Test;"                                                              +"\n"+
		            ""                                                                     +"\n"+
		            "int test1()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	Test st[2] ;"                                                   +"\n"+
		            "	st[0].a[0] = 1;"                                                     +"\n"+
		            "	st[1].a[1] = 1;  //FP,OOB"                                    +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OK"
		            ,
		            },
////////////////	/  36   ///////////////////	
		            {
		            "typedef struct _Test {"                                               +"\n"+
		            "	int a[2];"                                                           +"\n"+
		            "} Test;"                                                              +"\n"+
		            ""                                                                     +"\n"+
		            "int test1()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	Test *p;"                                                            +"\n"+
		            "	p->a[2] = 1;  //DEFECT,OOB,a"                                        +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OOB"
		            ,
		            },
////////////////	/  37   ///////////////////	
		            {
		            "typedef struct _Test {"                                               +"\n"+
		            "	int a[2];"                                                           +"\n"+
		            "} Test;"                                                              +"\n"+
		            ""                                                                     +"\n"+
		            "int test1()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	Test *p;"                                                            +"\n"+
		            "	p->a[1] = 1;  //FP,OOB"                                        +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OK"
		            ,
		            },	            
////////////////	/  38   ///////////////////	
		            {
		            "typedef struct _Test {"                                               +"\n"+
		            "	int a[3][3];"                                                        +"\n"+
		            "} Test;"                                                              +"\n"+
		            ""                                                                     +"\n"+
		            "int test1()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	Test st[2];"                                                   +"\n"+
		            "	st[1].a[0][3] = 1;  //DEFECT,OOB,a"                                  +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OOB"
		            ,
		            },   
////////////////	/  39   ///////////////////	
		            {
		            "typedef struct _Test {"                                               +"\n"+
		            "	int a[3][3];"                                                        +"\n"+
		            "} Test;"                                                              +"\n"+
		            ""                                                                     +"\n"+
		            "int test1()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	Test st[2] ;"                                                   +"\n"+
		            "	st[1].a[3][0] = 1;  //DEFECT,OOB,a"                                  +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OOB"
		            ,
		            }, 	            
////////////////	/  40   ///////////////////	
		            {
		            "typedef struct _Test {"                                               +"\n"+
		            "	int a[3][3];"                                                        +"\n"+
		            "} Test;"                                                              +"\n"+
		            ""                                                                     +"\n"+
		            "int test1()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	Test st[2] ;"                                                   +"\n"+
		            "	st[1].a[2][2] = 1;  //FP,OOB"                                  +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OK"
		            ,
		            }, 	            
////////////////	/  41   ///////////////////	
		            {
		            "char *ghx_oob_1_f1()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "    char mm[200];"                                                    +"\n"+
		            "	int cc;"                                                             +"\n"+
		            "	char ff;"                                                            +"\n"+
		            ""                                                                     +"\n"+
		            "	for (cc=0; cc<=200; cc++)"                                            +"\n"+
		            "	{"                                                                   +"\n"+
		            "		ff=mm[cc]; //DEFECT,OOB,mm"                                                +"\n"+
		            "	}"                                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OOB"
		            ,
		            },  
////////////////	/  42   ///////////////////	
		            {
		            "char *ghx_oob_1_f1()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "    char mm[200];"                                                    +"\n"+
		            "	int cc;"                                                             +"\n"+
		            "	char ff;"                                                            +"\n"+
		            ""                                                                     +"\n"+
		            "	for (cc=0; cc<300; cc++)"                                            +"\n"+
		            "	{"                                                                   +"\n"+
		            "		 "                                                +"\n"+
		            "	}"                                                                   +"\n"+
		            "	ff=mm[cc];////DEFECT,OOB,mm"                                                                     +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OOB"
		            ,
		            },         
/////////////////  43   ///////////////////	
		            {
		            "int k;"                                                               +"\n"+
		            "f1(int i){"                                                           +"\n"+
		            "char buf[10];"                                                        +"\n"+
		            "k=10;i=k;buf[i]=1;//参数局部化"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "f2(){"                                                                +"\n"+
		            "k=9;"                                                                +"\n"+
		            "f1(k);"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB"
		            ,
		            },		
/////////////////  44   ///////////////////	
		            {
		            ""                                                                     +"\n"+
		            "void yxh_oob_5_f1()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	int buf[4];"                                                         +"\n"+
		            "	char *p = (char *)buf;"                                              +"\n"+
		            "	p[12+3] = 'c';"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  45   ///////////////////	
		            {
		            "void yxh_oob_f1()"                                                    +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buf[13];"                                                       +"\n"+
		            "	int arr[4];"                                                         +"\n"+
		            ""                                                                     +"\n"+
		            "	((int *)buf)[4] = 1; //DEFECT"                                       +"\n"+
		            ""                                                                     +"\n"+
		            "	((char *)arr)[15] = 'c';"                                            +"\n"+
		            "	((char *)arr)[16] = 'c'; //DEFECT"                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB"
		            ,
		            },
	/////////////////  46   ///////////////////	
		            {
		            "void yxh_oob_f1()"                                                    +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buf[4];"                                                        +"\n"+
		            "	int i = 1, j = 2;"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "	//char c = (buf+j)[j]; //DEFECT"                                       +"\n"+
		            ""                                                                     +"\n"+
		            "	(buf+1)[2+i] = 'c'; //DEFECT"                                          +"\n"+
		            "	(buf+j)[i] = 'c';"                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB"
		            ,
		            }, 
///////////////// 47   ///////////////////	
		            {
		            "int k=9;"                                                               +"\n"+
		            "f1(){"                                                           +"\n"+
		            "k=10;"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "f2(){"                                                                +"\n"+
		            "int a[10];"                                                                +"\n"+
		            "f1();a[k]=5;"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB"
		            ,
		            }, 		   
	/////////////////  48   ///////////////////	
		            {
		            "void yxh_oob_f1()"                                                    +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buf[3];"                                                        +"\n"+
		            "	"                                                                    +"\n"+
		            "	*(buf+4) = 'c'; //DEFECT"                                            +"\n"+
		            "	char c = *(buf+4); //DEFECT"                                         +"\n"+
		            "	"                                                                    +"\n"+
		            "	char *q = buf+4; //DEFECT"                                           +"\n"+
		            "	char *p = (buf+4); //DEFECT"                                         +"\n"+
		            "	char *r;"                                                            +"\n"+
		            "	r = buf+4; //DEFECT"                                                 +"\n"+
		            "	r = (buf+4); //DEFECT"                                               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB"
		            ,
		            },		            
	/////////////////  49   ///////////////////	
		            {
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "char buf[10];"                                                        +"\n"+
		            "char *p=buf;"                                                         +"\n"+
		            "char ch=*(p+10);"                                                     +"\n"+
		            "//ch=p[7];"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB"
		            ,
		            },            
/////////////////  50   ///////////////////	
		            {
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "char buf[10];"                                                        +"\n"+
		            "char *p=buf;"                                                         +"\n"+		  
		            "char ch=(p+3)[7];"                                                         +"\n"+
		            "//p+=3;"                                                                +"\n"+
		            "//ch=p[7];"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB"
		            ,
		            },
/////////////////  50   ///////////////////	
		            {
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "char buf[10];"                                                        +"\n"+
		            "char *p=buf;"                                                         +"\n"+		  
		            "char ch;"                                                         +"\n"+
		            "p+=3;"                                                                +"\n"+
		            "ch=p[7];"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB"
		            ,
		            },		            
		 });
	 }
}
