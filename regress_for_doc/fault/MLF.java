package fault;

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
public class MLF
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

	public MLF(String source, String compiletype, String result)
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

/////////////////  1   ///////////////////	
        {
        "void foobar(int i)"                                                   +"\n"+
        "{"                                                                    +"\n"+
        "    char *p = (char*)malloc(12);"                                     +"\n"+
        "	if(i) {"                                                             +"\n"+
        "		p = NULL;"                                                          +"\n"+
        "	}"                                                                   +"\n"+
        "	return;"                                                             +"\n"+
        "}"                                                                    
        ,
        "gcc"
        ,
        "MLF"
        ,
        },
        
/////////////////  2   ///////////////////	
    {
    "void foo()"                                                           +"\n"+
    "{"                                                                    +"\n"+
    "	int *ptr = (int *)malloc(4);"                                        +"\n"+
    "	*ptr = 25;"                                                          +"\n"+
    "	ptr = (int *)malloc(4);"                                             +"\n"+
    "	*ptr = 35;"                                                          +"\n"+
    "}"                                                                    +"\n"+
    "void func(){"                                                         +"\n"+
    "	void foo();"                                                         +"\n"+
    "}"                                                                    
    ,
    "gcc"
    ,
    "MLF"
    ,
    },
      
/////////////////  3   ///////////////////	
    {
	"void f(){"                                                            +"\n"+
	"	int *memleak_error;"                                                 +"\n"+
	"	memleak_error=(int*)malloc(sizeof(int)*100);"                        +"\n"+
	"}"                                                                    
	,
	"gcc"
	,
	"MLF"
	,
	},

/////////////////  4   ///////////////////	
	{
	"void f(int a){"                                                       +"\n"+
	"	int *memleak_error;"                                                 +"\n"+
	"	memleak_error=(int*)malloc(sizeof(int)*100);"                        +"\n"+
	"	if(a>0)  return;"                                                    +"\n"+
	"	free(memleak_error);"                                                +"\n"+
	"}"                                                                    
	,
	"gcc"
	,
	"MLF"
	,
	},

/////////////////  5   ///////////////////	
{
"void f(int a,int b){"                                                 +"\n"+
"	int *memleak_error;"                                                 +"\n"+
"	memleak_error=(int*)malloc(sizeof(int)*100);"                        +"\n"+
"	if(a>0){"                                                            +"\n"+
"	if(!memleak_error){"                                                 +"\n"+
"		return;"                                                            +"\n"+
"	}"                                                                   +"\n"+
"	if(b<0){"                                                            +"\n"+
"		goto end;"                                                          +"\n"+
"	}"                                                                   +"\n"+
"	}"                                                                   +"\n"+
"	free(memleak_error);"                                                +"\n"+
"	end:"                                                                +"\n"+
"	return;"                                                             +"\n"+
"}"                                                                    
,
"gcc"
,
"MLF"
,
},
       
/////////////////  6   ///////////////////	
{
"void f(int a){"                                                       +"\n"+
"	int *memleak_error;"                                                 +"\n"+
"	memleak_error=(int*)malloc(sizeof(int)*100);"                        +"\n"+
"	if(a<0||!memleak_error)return;"                                      +"\n"+
"	free(memleak_error);"                                                +"\n"+
"}"                                                                    
,
"gcc"
,
"MLF"
,
},

/////////////////  7   ///////////////////	
{
"void f(){"                                                            +"\n"+
"	int *memleak_error3,*memleak_error4;"                                +"\n"+
"	memleak_error3=(int*)malloc(100);"                                   +"\n"+
"	memleak_error4=(int*)malloc(10);"                                    +"\n"+
"	if(!memleak_error3||!memleak_error4){"                               +"\n"+
"		return;"                                                            +"\n"+
"	}"                                                                   +"\n"+
"}"                                                                    
,
"gcc"
,
"MLF"
,
},

/////////////////  8   ///////////////////	
{
"int func2(int c)"                                                     +"\n"+
"{"                                                                    +"\n"+
"	char *p;"                                                            +"\n"+
"	p = (char *)malloc(sizeof (char) * 2);"                              +"\n"+
"	if (p == (void*)0)"                                                  +"\n"+
"		return 1;"                                                          +"\n"+
"	p = (void*)0;//DEFECT, MLF, p"                                       +"\n"+
"	free((char *)(p));"                                                  +"\n"+
"	return 1;"                                                           +"\n"+
"}"                                                                    
,
"gcc"
,
"MLF"
,
},

/////////////////  9   ///////////////////	
{
"void test(char *str)"                                                 +"\n"+
"{"                                                                    +"\n"+
"	char *p;"                                                            +"\n"+
"	p = strdup(str);"                                                    +"\n"+
"	if(p)"                                                               +"\n"+
"		printf(\"result: %s\\n\", p);"                                         +"\n"+
"	/* there's no free and p is a local variable */"                     +"\n"+
"	return;//DEFECT, MLF, p"                                             +"\n"+
"}"                                                                    
,
"gcc"
,
"MLF"
,
},


/////////////////  10   ///////////////////	
{
""                                                                     
,
"gcc"
,
"MLF"
,
},

/////////////////  11   ///////////////////	
{
""                                                                     
,
"gcc"
,
"MLF"
,
},


/////////////////  12   ///////////////////	
{
"void test8(int i){"                                                   +"\n"+
"	int *p;"                                                             +"\n"+
"	if(i>0){"                                                            +"\n"+
"		p=NULL;"                                                            +"\n"+
"	}else{"                                                              +"\n"+
"		p=(int *)malloc(8);"                                                +"\n"+
"	}"                                                                   +"\n"+
"	if(i>0){"                                                            +"\n"+
"		return;"                                                            +"\n"+
"	}"                                                                   +"\n"+
"}  //DEFECT, MLF, p"                                                  
,
"gcc"
,
"MLF"
,
},


/////////////////  13   ///////////////////	
{
"void *malloc(int nmemb);"                                             +"\n"+
"void free(void* p);"                                                  +"\n"+
"int * f5(){"                                                          +"\n"+
"	int *memleak_error6=NULL;"                                           +"\n"+
"	memleak_error6=(int*)malloc(100);"                                   +"\n"+
"	if(memleak_error6 != NULL){"                                         +"\n"+
"		return NULL;//DEFECT, MLF, memleak_error6"                          +"\n"+
"	}"                                                                   +"\n"+
"}"                                                                    
,
"gcc"
,
"MLF"
,
},

/////////////////  14   ///////////////////	
{
"void *malloc(int nmemb);"                                             +"\n"+
"void free(void* p);"                                                  +"\n"+
"void f7(int i){"                                                      +"\n"+
"	int a[5]={4,4,4,4,4,};"                                              +"\n"+
"	int* melleak_error8=NULL;"                                           +"\n"+
"	if(i>0){"                                                            +"\n"+
"		melleak_error8=a;"                                                  +"\n"+
"	}else{"                                                              +"\n"+
"		melleak_error8=(int*)malloc(100);"                                  +"\n"+
"	}"                                                                   +"\n"+
"	if(i>0){"                                                            +"\n"+
"		free(melleak_error8);"                                              +"\n"+
"	}"                                                                   +"\n"+
"}//DEFECT, MLF, melleak_error8"                                       
,
"gcc"
,
"MLF"
,
},

/////////////////  15   ///////////////////	
{
"void test4(){"                                                        +"\n"+
"	int *q=(int *)malloc(4);"                                            +"\n"+
"	if(var>10){"                                                         +"\n"+
"		free(q);"                                                           +"\n"+
"	}else{"                                                              +"\n"+
"	}"                                                                   +"\n"+
"}// DEFECT, MLF, q"                                                   
,
"gcc"
,
"MLF"
,
},


/////////////////  16   ///////////////////	
{
"void fuc(int a){"                                                     +"\n"+
"	char * x ;"                                                          +"\n"+
"	if (a) x= (char*)malloc(sizeof(char*));"                             +"\n"+
"	free(x);"                                                            +"\n"+
"}"                                                                    
,
"gcc"
,
"MLF"
,
},

/////////////////  17   ///////////////////	
{
"void f1(){"                                                           +"\n"+
"	int *memleak_error1=(int*)0;"                                        +"\n"+
"	memleak_error1 = (int *)malloc(4);"                                  +"\n"+
"	free(memleak_error1);"                                               +"\n"+
"	free(memleak_error1);//DEFECT, MLF, memleak_error1"                  +"\n"+
"}"                                                                    
,
"gcc"
,
"MLF"
,
},


/////////////////  18   ///////////////////	
{
"void f2(){"                                                           +"\n"+
"	int *memleak_error1;"                                                +"\n"+
"	memleak_error1 = (int *)malloc(8);"                                  +"\n"+
"	free(memleak_error1);"                                               +"\n"+
"	free(memleak_error1);//DEFECT,MLF, memleak_error1"                   +"\n"+
"}"                                                                    
,
"gcc"
,
"MLF"
,
},

/////////////////  19   ///////////////////	
{
"void test(char *str)"                                                 +"\n"+
"{"                                                                    +"\n"+
"	char *p;"                                                            +"\n"+
"	p = strdup(str);"                                                    +"\n"+
"	if(p) {"                                                             +"\n"+
"		printf(\"result: %s\\n\", p);"                                         +"\n"+
"		free(p);"                                                           +"\n"+
"		free(p);			//DEFECT, MLF, p"                                        +"\n"+
"	}"                                                                   +"\n"+
"}"                                                                    
,
"gcc"
,
"MLF"
,
},

/////////////////  20   ///////////////////	
{
"void test10(){"                                                       +"\n"+
"	int *p1,*p2,*p3;"                                                    +"\n"+
"	p2=(int *)malloc(4);"                                                +"\n"+
"	p3=(int *)malloc(4);"                                                +"\n"+
"	p1=p2;"                                                              +"\n"+
"	p1=p3;"                                                              +"\n"+
"	free(p1);"                                                           +"\n"+
"}//DEFECT, MLF, p2"                                                   
,
"gcc"
,
"MLF"
,
},

/////////////////  21   ///////////////////	
{
"void *malloc(int nmemb);"                                             +"\n"+
"void free(void* p);"                                                  +"\n"+
"int *p;"                                                              +"\n"+
"void f4(){"                                                           +"\n"+
"	int *memleak_error5=NULL,*not_memleak_error5=NULL;"                  +"\n"+
"	memleak_error5=(int*)malloc(100);"                                   +"\n"+
"	not_memleak_error5=(int*)malloc(10);"                                +"\n"+
"	p=not_memleak_error5; //assignment it to var that is global"         +"\n"+
"}//DEFECT, MLF, memleak_error5"                                       
,
"gcc"
,
"MLF"
,
},

/////////////////  22   ///////////////////	
{
"void *malloc(int nmemb);"                                             +"\n"+
"void free(void* p);"                                                  +"\n"+
"void f8(){"                                                           +"\n"+
"	int* melleak_error9=NULL;"                                           +"\n"+
"	melleak_error9=(int*)malloc(100);"                                   +"\n"+
"	melleak_error9++;//DEFECT, MLF, melleak_error9"                      +"\n"+
"	free(melleak_error9);"                                               +"\n"+
"}"                                                                    
,
"gcc"
,
"MLF"
,
},


/////////////////  23   ///////////////////	
{
"void test1(){"                                                        +"\n"+
"	int* p=(int *)malloc(44);"                                           +"\n"+
"	int* q=p;"                                                           +"\n"+
"	for(int i=0;i<10;i++){"                                              +"\n"+
"		(p++)[0]=i;// DEFECT, MLF, p"                                       +"\n"+
"	}		"                                                                 +"\n"+
"	free(p); "                                                           +"\n"+
"}"                                                                    
,
"gcc"
,
"MLF"
,
},

/////////////////  24   ///////////////////	
{
"void* malloc(int size);"                                              +"\n"+
"void free(void* p);"                                                  +"\n"+
"int* test1(){"                                                        +"\n"+
"	int* a=(int*)malloc(100);	"                                          +"\n"+
"	return a; // FP, MLF"                                                +"\n"+
"}	"                                                                   +"\n"+
"int* test2(){"                                                        +"\n"+
"	int* q=test1();"                                                     +"\n"+
"	return q;	"                                                          +"\n"+
"}"                                                                    +"\n"+
"void test3(){"                                                        +"\n"+
"	int* qq;"                                                            +"\n"+
"	qq=test2();"                                                         +"\n"+
"}// DEFECT, MLF, qq"                                                  
,
"gcc"
,
"MLF"
,
},

/////////////////  25   ///////////////////	
{
"int* test4(){"                                                        +"\n"+
"	int* a=(int*)malloc(100);	"                                          +"\n"+
"	return a; // FP, MLF"                                                +"\n"+
"}"                                                                    +"\n"+
"int* test5(){"                                                        +"\n"+
"	return test4();	"                                                    +"\n"+
"}"                                                                    +"\n"+
"void test6(){"                                                        +"\n"+
"	int* qq;"                                                            +"\n"+
"	qq=test5(); "                                                        +"\n"+
"}// DEFECT, MLF, qq"                                                  
,
"gcc"
,
"MLF"
,
},


/////////////////  26   ///////////////////	
{
"void test1(int** a){"                                                 +"\n"+
"	*a=(int*)malloc(100);	"                                              +"\n"+
"}"                                                                    +"\n"+
"void test2(){"                                                        +"\n"+
"	int* aa;"                                                            +"\n"+
"	test1(&aa);"                                                         +"\n"+
"}//DEFECT, MLF, aa"                                                   
,
"gcc"
,
"MLF"
,
},

/////////////////  27   ///////////////////	
{
"char *new1(){"                                                        +"\n"+
"	return (char *)malloc(12);"                                          +"\n"+
"}"                                                                    +"\n"+
"void test1(){"                                                        +"\n"+
"	char *p=new1();"                                                     +"\n"+
"	free(p);// DEFECT, MLF, p"                                           +"\n"+
"}"                                                                    
,
"gcc"
,
"MLF"
,
},

/////////////////  28   ///////////////////	
{
"//class A{"                                                           +"\n"+
"//	void foo();"                                                       +"\n"+
"//};"                                                                 +"\n"+
"//void A::foo()"                                                      +"\n"+
"void foo()"                                                           +"\n"+
"{"                                                                    +"\n"+
"	int *ptr;"                                                           +"\n"+
"	ptr = (int*)malloc(sizeof(int));"                                    +"\n"+
"	free(ptr);"                                                          +"\n"+
"}"                                                                    +"\n"+
"void func(){"                                                         +"\n"+
"	foo();"                                                              +"\n"+
"}"                                                                    
,
"gcc"
,
"MLF"
,
},

/////////////////  29   ///////////////////	
{
"char* new2() {"                                                       +"\n"+
"	return (char *)malloc(1);"                                           +"\n"+
"}"                                                                    +"\n"+
"void test2(){"                                                        +"\n"+
"	char *p=new2();"                                                     +"\n"+
"	free(p);// DEFECT, MLF, p"                                           +"\n"+
"}"                                                                    
,
"gcc"
,
"MLF"
,
},

/////////////////  30   ///////////////////	
{
""                                                                     
,
"gcc"
,
"MLF"
,
},


/////////////////  31   ///////////////////	
{
""                                                                     
,
"gcc"
,
"MLF"
,
},





		});
	}
}
