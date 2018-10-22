package softtest.test.gcc.rules.fault;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

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
import softtest.fsmanalysis.c.CAnalysis;
import softtest.fsmanalysis.c.FSMAnalysisVisitor;
import softtest.fsmanalysis.c.FSMControlFlowData;
import softtest.fsmanalysis.c.Report;
import softtest.interpro.c.InterCallGraph;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.InterMethodVisitor;
import softtest.pretreatment.PlatformType;
import softtest.pretreatment.Pretreatment;
import softtest.summary.lib.c.LibManager;
import softtest.symboltable.c.AbstractScope;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.OccurrenceAndExpressionTypeFinder;
import softtest.symboltable.c.ScopeAndDeclarationFinder;

@RunWith(Parameterized.class)
public class Test_MLF
{
	private String source = null;

	private String compiletype = null;

	private String result = null;

	private static final String fsmPath = "softtest/rules/gcc/fault/MLF-0.1.xml";

	// private static final String LIB_SUMMARYS_PATH="gcc_lib/rm_summary.xml";
	FSMAnalysisVisitor fsmAnalysis;

	private FSMControlFlowData cfData;

	static Pretreatment pre = new Pretreatment();

	static LibManager libManager = LibManager.getInstance();

	InterContext interContext = InterContext.getInstance();

	static int testcaseNum = 0;

	String temp;// 预处理后的中间文件

	public Test_MLF(String source, String compiletype, String result)
	{
		this.source = source;
		this.compiletype = compiletype;
		this.result = result;
	}

	@BeforeClass
	public static void setUpBase()
	{
		// 根据待测试模式XML文件路径初始化自动机列表
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);

		// 加载库函数摘要
		// libManager.loadSingleLibFile(LIB_SUMMARYS_PATH);
		CAnalysis.deleteAndCreateTemp(Config.PRETREAT_DIR);
		pre.setPlatform(PlatformType.GCC);
		String INCLUDE = System.getenv("GCCINC");
		if (INCLUDE == null)
		{
			throw new RuntimeException(
					"System environment variable \"GCCINC\" error!");
		}
		String[] Inctemp = INCLUDE.split(";");
		// 将GCCINC中的头文件目录，自动识别为头文件目录
		List<String> include = new ArrayList<String>();
		for (int i = 0; i < Inctemp.length; i++)
		{
			Pretreatment.systemInc.add(Inctemp[i]);
			include.add(Inctemp[i]);
		}
		pre.setInclude(include);
		// ZYS:最好根据状态机描述文件XML中的相关字段读取出该模式所属于的故障类别
		fsm.setType("fault");
		// 每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);

		Config.REGRESS_RULE_TEST = true;
	}

	// 根据不同的模式需求，自行分配当前AST分析到的步骤
	private void analysis(ASTTranslationUnit astroot)
	{
		astroot.jjtAccept(new ScopeAndDeclarationFinder(), null);
		astroot.jjtAccept(new OccurrenceAndExpressionTypeFinder(), null);

		// 清空原有全局分析中产生的函数摘要信息
		InterCallGraph.getInstance().clear();
		astroot.jjtAccept(new InterMethodVisitor(), null);

		CGraph g = new CGraph();
		((AbstractScope) (astroot.getScope())).resolveCallRelation(g);
		List<CVexNode> list = g.getTopologicalOrderList();
		Collections.reverse(list);

		ControlFlowData flow = new ControlFlowData();
		ControlFlowVisitor cfv = new ControlFlowVisitor();
		ControlFlowDomainVisitor cfd = new ControlFlowDomainVisitor();

		for (CVexNode cvnode : list)
		{
			SimpleNode node = cvnode.getMethodNameDeclaration().getNode();
			if (node instanceof ASTFunctionDefinition)
			{
				cfv.visit((ASTFunctionDefinition) node, flow);
				cfd.visit((ASTFunctionDefinition) node, null);
			}
		}

		astroot.jjtAccept(fsmAnalysis, cfData);

		assertEquals(result, getFSMAnalysisResult());
	}

	private String getFSMAnalysisResult()
	{
		List<Report> reports = cfData.getReports();
		String analysisResult = null;
		if (reports.size() == 0)
		{
			analysisResult = "OK";
			return analysisResult;
		}
		for (Report r : reports)
		{
			analysisResult = r.getFsmName();
			System.out.println(r.getFsmName() + " : " + r.getDesp());
		}
		return analysisResult;
	}

	@Before
	public void init()
	{
		cfData = new FSMControlFlowData();
		List<Report> reports = new ArrayList<Report>();
		cfData.setReports(reports);
		fsmAnalysis = new FSMAnalysisVisitor(cfData);

		// 将测试用例中的代码行，写到temp中形成.c源文件；
		String tempName = "testcase_" + (testcaseNum++) + ".c";
		File tempFile = new File(Config.PRETREAT_DIR + "\\" + tempName);
		if (Config.DELETE_PRETREAT_FILES)
		{
			tempFile.deleteOnExit();
		}
		FileWriter fw;
		try
		{
			fw = new FileWriter(tempFile);
			fw.write(source);
			fw.flush();
		}
		catch (IOException e)
		{
			e.printStackTrace();
		}

		temp = pre.pretreat(tempFile.getAbsolutePath(), pre.getInclude(),
				new ArrayList<String>());

		// 根据当前检测的测试用例，载入相关的库函数摘要
		Set<MethodNameDeclaration> libDecls = libManager.compileLib(pre
				.getLibIncludes());
		interContext = InterContext.getInstance();
		interContext.addLibMethodDecl(libDecls);
	}

	@After
	public void shutdown()
	{
		// 每个测试用例分析完毕，都清空本次生成的库函数摘要信息
		interContext.getLibMethodDecls().clear();
	}

	@Test
	public void test()
	{
		try
		{
			CParser.setType("gcc");
			CParser parser_gcc;
			parser_gcc = CParser.getParser(new CCharStream(new FileInputStream(
					temp)));
			CParser.setType("keil");
			CParser parser_keil = CParser.getParser(new CCharStream(
					new FileInputStream(temp)));
			ASTTranslationUnit gcc_astroot = null, keil_astroot = null;
			if (compiletype.equals("gcc"))
			{
				CParser.setType("gcc");
				try
				{
					gcc_astroot = parser_gcc.TranslationUnit();
				}
				catch (ParseException e)
				{
					e.printStackTrace();
					fail("parse error");
				}
				analysis(gcc_astroot);
			}
			else
				if (compiletype.equals("keil"))
				{
					CParser.setType("keil");
					try
					{
						keil_astroot = parser_keil.TranslationUnit();
					}
					catch (ParseException e)
					{
						e.printStackTrace();
						fail("parse error");
					}
					analysis(keil_astroot);
				}
				else
				{
					CParser.setType("gcc");
					try
					{
						gcc_astroot = parser_gcc.TranslationUnit();
					}
					catch (ParseException e)
					{
						e.printStackTrace();
						fail("parse error");
					}
					pre.setPlatform(PlatformType.GCC);
					analysis(gcc_astroot);

					CParser.setType("keil");
					try
					{
						keil_astroot = parser_keil.TranslationUnit();
					}
					catch (ParseException e)
					{
						e.printStackTrace();
						fail("parse error");
					}
					pre.setPlatform(PlatformType.KEIL);
					analysis(keil_astroot);
				}
		}
		catch (FileNotFoundException e1)
		{
			e1.printStackTrace();
		}
	}

	@Parameters
	public static Collection<Object[]> testcaseAndResults()
	{
		return Arrays.asList(new Object[][] {	

///////////////// 0  ///////////////////	
            {
	        "#include<stdlib.h>"                                                   +"\n"+
	        "char * xmalloc()"                                                     +"\n"+
            "{"                                                                    +"\n"+
            "    char *mem;"                                 +"\n"+
           "     mem = (char *)calloc(10, 1);"                                 +"\n"+
             "   return mem;"                                 +"\n"+
            "}"                                                                    +"\n"+
            "int main()"                                                           +"\n"+
            "{"                                                                    +"\n"+
            "    char *p;"                                                         +"\n"+
            "    p=xmalloc();"                                                     +"\n"+
            "    return 0;"                                                        +"\n"+
            "    }"                                                                
            ,
            "gcc"
            ,
            "MLF"
            ,
            },
/////////////////  1  ///////////////////	
        {
        "#include<stdlib.h>"                                                   +"\n"+
        "void *__ckd_malloc__(int32 size)"                                       +"\n"+
        "{"                                                                    +"\n"+
        "    void *mem;"                                                       +"\n"+
        "    mem = malloc(size);"                                              +"\n"+
        "    return mem;"                                                      +"\n"+
        "}"                                                                    +"\n"+
        ""                                                                     +"\n"+
        "void ** __ckd_calloc_2d__( )"                                         +"\n"+
        "{"                                                                    +"\n"+
        "     float32 **ref;"                                                     +"\n"+
        "     ref = (char **) __ckd_malloc__(16);"                             +"\n"+
        "     return ((void **) ref);"                                         +"\n"+
        "}"                                                                    +"\n"+
        ""                                                                     +"\n"+
        "int read_cep(float32 ***cep)"                                           +"\n"+
        "{"                                                                    +"\n"+
        "  float32 **mfcbuf;"                                                  +"\n"+
        "  mfcbuf = (float32 **)__ckd_calloc_2d__( );"                              +"\n"+
        "  *cep = mfcbuf;"                                                     +"\n"+
        "  return 0;"                                                          +"\n"+
        "}"                                                                    +"\n"+
        "int main(int argc, char *argv[])"                                     +"\n"+
        "{"                                                                    +"\n"+
        "  float32  **cep;"                                                      +"\n"+
        "  if (read_cep(&cep) == 0)"                                           +"\n"+
        "     return 0;"                                                       +"\n"+
        "}"                                                                    
        ,
        "gcc"
        ,
        "MLF"
        ,
        },

///////////////  1   ///////////////////	
    {
    "#include<stdlib.h>"                                                   +"\n"+
    ""                                                                     +"\n"+
    "int read_cep(float **cep)"                                            +"\n"+
    "{"                                                                    +"\n"+
    "  char *mfcbuf;"                                                   +"\n"+
    "  mfcbuf = malloc(10);"                                               +"\n"+
    "  *cep = mfcbuf;"                                                     +"\n"+
    "  return 0;"                                                          +"\n"+
    "}"                                                                    +"\n"+
    "int main(int argc, char *argv[])"                                     +"\n"+
    "{"                                                                    +"\n"+
    "  char  *cep;"                                                       +"\n"+
    "  if (read_cep(&cep) == 0)"                                           +"\n"+
    "     return 0;"                                                       +"\n"+
    "}"                                                                    
    ,
    "gcc"
    ,
    "MLF"
    ,
    },
/////////////////  1   ///////////////////	
//{
//"#include<stdlib.h>"                                                   +"\n"+
//""                                                                     +"\n"+
//"int read_cep(char **cep)"                                            +"\n"+
//"{"                                                                    +"\n"+
//"  int a = 0;"                                                     +"\n"+
//"  *cep = (char *)malloc(12);"                                                     +"\n"+
//"  return a;"                                                          +"\n"+
//"}"                                                                    +"\n"+
//"int main(int argc, char *argv[])"                                     +"\n"+
//"{"                                                                    +"\n"+
//"  char  *cep;"                                                       +"\n"+
//"  if (read_cep(&cep) == 0)"                                           +"\n"+
//"     return 0;"                                                       +"\n"+
//"}"                                                                    
//,
//"gcc"
//,
//"MLF"
//,
//},
/////////////////  2   ///////////////////	
	            {
	            "#include<stdlib.h>"                                                   +"\n"+
	            "int foo0()                          "                                 +"\n"+
	            "{"                                                                    +"\n"+
	            "	int *a = (int *)malloc(sizeof(int)*1);"                              +"\n"+
	            "	free(a);"                                                            +"\n"+
	            "	"                                                                    +"\n"+
	            "	return 0;"                                                           +"\n"+
	            "} "                                                                   
	            ,
	            "gcc"
	            ,
	            "OK"
	            ,
	            },

	///////////////// 3 ///////////////////	
	            {
	            "#include<stdlib.h>"                                                   +"\n"+
	            "int foo1()"                                                           +"\n"+
	            "{"                                                                    +"\n"+
	        //    "	int *a = (int *)malloc(sizeof(int)*1);"                              +"\n"+
	            "	int *b = (int *)malloc(sizeof(int)*1);"                              +"\n"+
	            "	return 0;"                                                           +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "MLF"
	            ,
	            },

	/////////////////  2   ///////////////////	
	            {
	            "#include<stdlib.h>"                                                   +"\n"+
	            "void foo2(int a)"                                                     +"\n"+
	            " {"                                                                   +"\n"+
	            "	int *p= (int *)malloc(sizeof(int)*1);"                               +"\n"+
	            "	"                                                                    +"\n"+
	            "	if(a>0)"                                                             +"\n"+
	            "		return;"                                                            +"\n"+
	            "	"                                                                    +"\n"+
	            "	free(p);"                                                            +"\n"+
	            " } "                                                                  
	            ,
	            "gcc"
	            ,
	            "MLF"
	            ,
	            },

	/////////////////  3   ///////////////////	
	            {
	            "#include<stdlib.h>"                                                   +"\n"+
	            "void foo4()"                                                          +"\n"+
	            " {"                                                                   +"\n"+
	            "	int *a = (int *)malloc(sizeof(int)*1);"                              +"\n"+
	            "	int *b = (int *)malloc(sizeof(int)*1);"                              +"\n"+
	            "	"                                                                    +"\n"+
	            "	if(!a || !b)"                                                        +"\n"+
	            "	{"                                                                   +"\n"+
	            "		return ;"                                                           +"\n"+
	            "	}"                                                                   +"\n"+
	            "	"                                                                    +"\n"+
	            "	free(a);"                                                            +"\n"+
	            "	free(b);"                                                            +"\n"+
	            " } "                                                                  
	            ,
	            "gcc"
	            ,
	            "MLF"
	            ,
	            },

	/////////////////  4   ///////////////////	
	            {
	            "#include<stdlib.h>"                                                   +"\n"+
	            "void foo5()"                                                          +"\n"+
	            " {"                                                                   +"\n"+
	            "	int *a = (int *)malloc(sizeof(int)*10);"                             +"\n"+
	            "	a++;"                                                                +"\n"+
	            "	free(a);"                                                            +"\n"+
	            " } "                                                                  
	            ,
	            "gcc"
	            ,
	            "MLF"
	            ,
	            },
	///////////////  5  ///////////////////
	            {
		            "#include<stdlib.h>"                                                   +"\n"+
		            "int *foo11(int size)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	int *a = (int *)malloc(sizeof(int)*size);"                         +"\n"+
		            "	"                                                                  +"\n"+
		            "	return a;"                                                         +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void foo10()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	int size = 1;"                                                     +"\n"+
		            "	int *a = foo11(size);"                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "MLF"
		            ,
		            },
	///////////////// k9   ///////////////////	///////////////// k9   ///////////////////					
	///////////////// k9   ///////////////////	///////////////// k9   ///////////////////	
	///////////////// k9  ///////////////////	///////////////// k9   ///////////////////	

			
	/////////////////  6   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            "#include<string.h>"                                                   +"\n"+
		            "char *retrieve_input_string() "                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "  char fname[50]; "                                                   +"\n"+
		            "  printf(\"please input file name: \");"                                +"\n"+
		            "  scanf(\"%s\",fname);"                                                 +"\n"+
		            "  return strdup(fname); "                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int main(int argc, char *argv[])"                                     +"\n"+
		            "{"                                                                    +"\n"+
		            "  char *line;"                                                        +"\n"+
		            "  if ((!(line = retrieve_input_string()) )) "                            +"\n"+
		            "  return 0;	"                                                  +"\n"+
		            //    "     printf (\"the input string is: %s\" , line) ;"                     +"\n"+
		         
		            "  system(\"PAUSE\");	"                                                  +"\n"+
		       //     "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "MLF"
		            ,
		            },


	///////////////// 7 ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            "#include<string.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "struct Student"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            " 		union"                                                             +"\n"+
		            "   		{"                                                               +"\n"+
		            "     		 char ab[4];"                                                  +"\n"+
		            "     		 int bdummy;"                                                  +"\n"+
		            "  		}u;"                                                              +"\n"+
		            "};"                                                                   +"\n"+
		            "int main(int argc, char *argv[])"                                     +"\n"+
		            "{ "                                                                   +"\n"+
		            "  struct Student *p = (struct Student *)malloc(sizeof(struct Student));"+"\n"+
		            "//p->u.bdummy = 2;"                                                     +"\n"+
		            "system(\"PAUSE\");	"                                                    +"\n"+
		            "return p->u.bdummy;"                                                  +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "MLF"
		            ,
		            },
		            
		            
	/////////////////  8   ///////////////////	
		            {
		            "#include<stdlib.h>"                                                   +"\n"+
		            "#include<stdio.h>"                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "typedef struct "                                                      +"\n"+
		            "{"                                                                    +"\n"+
		            "	char IP[8];"                                                         +"\n"+
		            "	int  protocol;"                                                      +"\n"+
		            "	int  k[10];"                                                         +"\n"+
		            "	int  num;"                                                           +"\n"+
		            "	int  isKnown;"                                                       +"\n"+
		            "}CipherRec, *pCipherRec;"                                             +"\n"+
		            ""                                                                     +"\n"+
		            "void func(){"                                                         +"\n"+
		            ""                                                                     +"\n"+
		            "pCipherRec szTemFound;"                                               +"\n"+
		            "szTemFound = (pCipherRec)malloc(sizeof(CipherRec)*65536);"            +"\n"+
		            "*szTemFound;"                                                         +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "MLF"                                                        
		            ,
		            },
		            
	/////////////////  9   ///////////////////	
		            {
		            "#include<stdlib.h>"                                                   +"\n"+
		            "#include<stdio.h>"                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "typedef struct "                                                      +"\n"+
		            "{"                                                                    +"\n"+
		            "	char IP[8];"                                                         +"\n"+
		            "	int  protocol;"                                                      +"\n"+
		            "	int  k[10];"                                                         +"\n"+
		            "	int  num;"                                                           +"\n"+
		            "	int  isKnown;"                                                       +"\n"+
		            "}CipherRec, *pCipherRec;"                                             +"\n"+
		            ""                                                                     +"\n"+
		            "void func1(){"                                                        +"\n"+
		            ""                                                                     +"\n"+
		            "pCipherRec szTemFound;"                                               +"\n"+
		            "szTemFound = (pCipherRec)malloc(sizeof(CipherRec)*65536);"            +"\n"+
		            "*szTemFound;"                                                         +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(){"                                                        +"\n"+
		            "	func1();"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "MLF"                                                        
		            ,
		            },

	/////////////////  10   ///////////////////	
		            {
		            "#include<stdlib.h>"                                                   +"\n"+
		            "#include<stdio.h>"                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "typedef struct "                                                      +"\n"+
		            "{"                                                                    +"\n"+
		            "	char IP[8];"                                                         +"\n"+
		            "	int  protocol;"                                                      +"\n"+
		            "	int  k[10];"                                                         +"\n"+
		            "	int  num;"                                                           +"\n"+
		            "	int  isKnown;"                                                       +"\n"+
		            "}CipherRec, *pCipherRec;"                                             +"\n"+
		            ""                                                                     +"\n"+
		            "void func1(){"                                                        +"\n"+
		            ""                                                                     +"\n"+
		            "pCipherRec szTemFound1;"                                              +"\n"+
		            "szTemFound1 = (pCipherRec)malloc(sizeof(CipherRec)*65536);"           +"\n"+
		            "return szTemFound1;"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(){"                                                        +"\n"+
		            "	pCipherRec szTemFound2=func1();"                                     +"\n"+
		            "	return szTemFound2;"                                                 +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func3(){"                                                        +"\n"+
		            "	pCipherRec szTemFound3;"                                             +"\n"+
		            "	szTemFound3=func1();	"                                               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "MLF"                                                        
		            ,
		            },

	/////////////////  11   ///////////////////	
		            {
		            "#include<stdlib.h>"                                                   +"\n"+
		            "#include<stdio.h>"                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "typedef struct "                                                      +"\n"+
		            "{"                                                                    +"\n"+
		            "	char IP[8];"                                                         +"\n"+
		            "	int  protocol;"                                                      +"\n"+
		            "	int  k[10];"                                                         +"\n"+
		            "	int  num;"                                                           +"\n"+
		            "	int  isKnown;"                                                       +"\n"+
		            "}CipherRec, *pCipherRec;"                                             +"\n"+
		            ""                                                                     +"\n"+
		            "void func1(int a){"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "pCipherRec szTemFound;"                                               +"\n"+
		            "szTemFound = (pCipherRec)malloc(sizeof(CipherRec)*65536);"            +"\n"+
		            "if(a<0||!szTemFound)return;"                                          +"\n"+
		            "free(szTemFound);"                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "MLF"                                                       
		            ,
		            },

		});
	}
}
