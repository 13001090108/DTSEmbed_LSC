package softtest.test.c.gcc.test_team_1;

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
/////////////////  0   ///////////////////	
	            {
	            "#include \"stdlib.h\""                                                  +"\n"+
	            "void ghx_mlf_3_f3()"                                                  +"\n"+
	            "{"                                                                    +"\n"+
	            "	int *m=NULL;"                                                        +"\n"+
	            "	if((m=(int*)malloc(100))!=NULL)"                                     +"\n"+
	            "	{"                                                                   +"\n"+
	            "		return;//DEFECT"                                                    +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "MLF"
	            ,
	            },
/////////////////  1   ///////////////////	
	            //指针区间计算异常，另外不知道是不是区间计算错误的缘故，在FSMStateInstance::calDomain中同一变量不同状态下的值会合并
	            {
	            "#include \"stdlib.h\""                                                  +"\n"+
	            "void ghx_mlf_4_f4(int i)"                                             +"\n"+
	            "{"                                                                    +"\n"+
	            "	int a[5]={4,4,4,4,4,};"                                              +"\n"+
	            "	int* m4=NULL;"                                                       +"\n"+
	            "	if(i>0){"                                                            +"\n"+
	            "		m4=a;"                                                              +"\n"+
	            "	}else{"                                                              +"\n"+
	            "		m4=(int*)malloc(100);"                                              +"\n"+
	            "	}"                                                                   +"\n"+
	            "	if(i>0)//DEFECT"                                                     +"\n"+
	            "	{"                                                                   +"\n"+
	            "		free(m4);"                                                          +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "MLF"
	            ,
	            },
/////////////////  2   ///////////////////
	          //指针区间计算异常，另外不知道是不是区间计算错误的缘故，在FSMStateInstance::calDomain中同一变量不同状态下的值会合并
	          //20100726测试用例2和测试用例1出错的原因是 在FSMStateInstance::calDomain中同一变量不同状态下的值会合并
	            {
	            "#include \"stdlib.h\""                                                  +"\n"+
	            "void ghx_mlf_4_f5(int i)"                                             +"\n"+
	            "{"                                                                    +"\n"+
	            "	int a[5]={4,4,4,4,4,};"                                              +"\n"+
	            "	int* m4=NULL;"                                                       +"\n"+
	            "	if(i>0){"                                                            +"\n"+
	            "		m4=a;"                                                              +"\n"+
	            "	}else{"                                                              +"\n"+
	            "		m4=(int*)malloc(100);"                                              +"\n"+
	            "	}"                                                                   +"\n"+
	            "	if(i<=0)//FP"                                                        +"\n"+
	            "	{"                                                                   +"\n"+
	            "		free(m4);"                                                          +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "OK"
	            ,
	            },
/////////////////  3   ///////////////////	
	            {
	            "#include <malloc.h>"                                                  +"\n"+
	            "#include <stdio.h>"                                                   +"\n"+
	            "void ghx_mlf_5_f5()"                                                  +"\n"+
	            "{"                                                                    +"\n"+
	            "char *p = (char*)malloc(100);"                                        +"\n"+
	            ""                                                                     +"\n"+
	            "delete(p); //DEFECT"                                                  +"\n"+
	            "  "                                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "MLF"
	            ,
	            },
/////////////////  4   ///////////////////	
	            {
	            "#include <malloc.h>"                                                  +"\n"+
	            "#include <stdio.h>"                                                   +"\n"+
	            ""                                                                     +"\n"+
	            "void ghx_mlf_5_f1(int i)"                                             +"\n"+
	            "{"                                                                    +"\n"+
	            "char *p=(char*)malloc(100);"                                          +"\n"+
	            "free(p);"                                                             +"\n"+
	            "if(i>0)"                                                              +"\n"+
	            "free(p);//DEFECT"                                                     +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "MLF"
	            ,
	            },
/////////////////  5   ///////////////////	
	            {
	            "#include <malloc.h>"                                                  +"\n"+
	            "#include <stdio.h>"                                                   +"\n"+
	            ""                                                                     +"\n"+
	            "void ghx_mlf_5_f2()"                                                  +"\n"+
	            "{"                                                                    +"\n"+
	            "char *p = (char*)malloc(100);"                                        +"\n"+
	            ""                                                                     +"\n"+
	            "free(p); //FP"                                                        +"\n"+
	            "  "                                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "OK"
	            ,
	            },
/////////////////  6   ///////////////////	
	            {
	            "#include \"stdio.h\""                                                   +"\n"+
	            "#include \"stdlib.h\""                                                  +"\n"+
	            "void ghx_mlf_6_f6()"                                                  +"\n"+
	            "{"                                                                    +"\n"+
	            "int i;"                                                               +"\n"+
	            "char* p2 = (char*)malloc(5*sizeof(char));"                            +"\n"+
	            ""                                                                     +"\n"+
	            "for( i=0; i< 5; i++ )"                                                +"\n"+
	            "{"                                                                    +"\n"+
	            "printf(\"abc\");"                                                       +"\n"+
	            "}"                                                                    +"\n"+
	            "delete(p2);//DEFECT"                                                  +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "MLF"
	            ,
	            },
/////////////////  7   ///////////////////	
	            {
	            "#include <malloc.h>"                                                  +"\n"+
	            "#include <stdio.h>"                                                   +"\n"+
	            "void jhb_mlf_4_f1(unsigned int i)"                                    +"\n"+
	            "{"                                                                    +"\n"+
	            "char *p = (char*)malloc(12);"                                         +"\n"+
	            "if(i>0) {"                                                            +"\n"+
	            "free(p); "                                                            +"\n"+
	            "}"                                                                    +"\n"+
	            "return;//DEFECT"                                                      +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "MLF"
	            ,
	            },
/////////////////  8   ///////////////////	
	            {
	            "#include <malloc.h>"                                                  +"\n"+
	            "#include <stdio.h>"                                                   +"\n"+
	            ""                                                                     +"\n"+
	            "void f(unsigned int i){"                                              +"\n"+
	            "	int *memleak_error=(int*)malloc(1);"                                 +"\n"+
	            "	*memleak_error = 10;"                                                +"\n"+
	            "    if (i>0) return;"                                                 +"\n"+
	            "	free(memleak_error);   //DEFECT"                                     +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "MLF"
	            ,
	            },
/////////////////  9   ///////////////////	
	            {
	            "#include <stdlib.h>"                                                  +"\n"+
	            ""                                                                     +"\n"+
	            "void foo()"                                                           +"\n"+
	            "{"                                                                    +"\n"+
	            " int *ptr = (int*)malloc(1);"                                         +"\n"+
	            " *ptr = 25;"                                                          +"\n"+
	            " ptr = (int*)malloc(1); //DEFECT"                                     +"\n"+
	            " *ptr = 35;"                                                          +"\n"+
	            "}"                                                           
	            ,
	            "gcc"
	            ,
	            "MLF"
	            ,
	            },
/////////////////  10   ///////////////////	
	            {
	            "#include <stdlib.h>"                                                  +"\n"+
	            ""                                                                     +"\n"+
	            "int* func()"                                                          +"\n"+
	            "{"                                                                    +"\n"+
	            "	int *ptr = (int*)malloc(1);"                                         +"\n"+
	            ""                                                                     +"\n"+
	            "	return ptr ? ptr : (int*)malloc(1);"                                 +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "OK"
	            ,
	            },

/**********************************************以下测试用例来此test_team_1/MLF_PRE****************************************************/

/////////////////  11   ///////////////////	
				//qian:result:MLF
	            {
	            "#include <stdlib.h>"                                                  +"\n"+
	            "void fun1(int flag,int *p){"                                          +"\n"+
	            "	if(flag)"                                                            +"\n"+
	            "		free(p);"                                                           +"\n"+
	            ""                                                                     +"\n"+
	            "}"                                                                    +"\n"+
	            "void f(int flag){"                                                    +"\n"+
	            "	int *p=(int*)malloc(1);"                                             +"\n"+
	            "	fun1(flag,p);  //DEFECT"                                             +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
//	            "MLF_PRE"
	            "MLF"
	            ,
	            },
/////////////////  12   ///////////////////	
	            //qian:result:OK
	            {
	            "#include <stdlib.h>"                                                  +"\n"+
	            ""                                                                     +"\n"+
	            "void fun2(int *p){"                                                   +"\n"+
	            ""                                                                     +"\n"+
	            "		free(p);"                                                           +"\n"+
	            ""                                                                     +"\n"+
	            "}"                                                                    +"\n"+
	            "void f(int flag){"                                                    +"\n"+
	            "	int *q=(int*)malloc(1);"                                             +"\n"+
	            "	fun2(q);   //FP"                                                     +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "OK"
	            ,
	            },
/////////////////  13   ///////////////////	
	            //qian:result:OK
	            {
	            "#include <stdlib.h>"                                                  +"\n"+
	            "void fun2(int *p){"                                                   +"\n"+
	            "		free(p);"                                                           +"\n"+
	            ""                                                                     +"\n"+
	            "}"                                                                    +"\n"+
	            "void fun3(int *p){"                                                   +"\n"+
	            "	fun2(p);"                                                            +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "void f(int flag){"                                                    +"\n"+
	            "	int *p=(int*)malloc(1);"                                             +"\n"+
	            "	"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "	fun3(p);   //FP"                                                     +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "OK"
	            ,
	            },
/////////////////  14   ///////////////////	
	            //qian:result:MLF  错报 正在修改中
	            {
	            "#include <stdlib.h>"                                                  +"\n"+
	            "int flag;"                                                            +"\n"+
	            "void fun2(int *p){"                                                   +"\n"+
	            "        if(p)"                                                        +"\n"+
	            "		   free(p);"                                                        +"\n"+
	            ""                                                                     +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "void f(){"                                                            +"\n"+
	            "	int *p=(int*)malloc(1);"                                             +"\n"+
	            "	fun2(p);"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "OK"
	            ,
	            },
/////////////////  15   ///////////////////	
	            //qian：result：MLF
	            {
	            "#include <stdlib.h>"                                                  +"\n"+
	            ""                                                                     +"\n"+
	            "char* func2(int);"                                                    +"\n"+
	            "char* func3();"                                                       +"\n"+
	            ""                                                                     +"\n"+
	            "void func1(int flag)"                                                 +"\n"+
	            "{"                                                                    +"\n"+
	            "	char *ptr;"                                                          +"\n"+
	            ""                                                                     +"\n"+
	            "	ptr = func2(flag);"                                                  +"\n"+
	            "	if (ptr) {"                                                          +"\n"+
	            "		*ptr = 3;"                                                          +"\n"+
	            "	}"                                                                   +"\n"+
	            "	return; //DEFECT"                                                    +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "char* func2(int flag)"                                                +"\n"+
	            "{"                                                                    +"\n"+
	            "	char *ptr = NULL;"                                                   +"\n"+
	            ""                                                                     +"\n"+
	            "	if (flag > 0) {"                                                     +"\n"+
	            "		ptr = (char*)malloc(sizeof(char));"                                 +"\n"+
	            "	} else {"                                                            +"\n"+
	            "		ptr = func3();"                                                     +"\n"+
	            "	}"                                                                   +"\n"+
	            ""                                                                     +"\n"+
	            "	return ptr;"                                                         +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "char* func3()"                                                        +"\n"+
	            "{"                                                                    +"\n"+
	            "	char *ptr;"                                                          +"\n"+
	            ""                                                                     +"\n"+
	            "	ptr = (char*)malloc(5*sizeof(char));"                                +"\n"+
	            "	if (ptr) {"                                                          +"\n"+
	            "		return ptr;"                                                        +"\n"+
	            "	} else {"                                                            +"\n"+
	            "		return NULL;"                                                       +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
//	            "MLF_PRE"
	            "MLF"
	            ,
	            },
/////////////////  16   ///////////////////	
	            //qian:result:MLF
	            {
	            "#include <stdlib.h>"                                                  +"\n"+
	            ""                                                                     +"\n"+
	            "char* func2(int);"                                                    +"\n"+
	            "char* func3();"                                                       +"\n"+
	            ""                                                                     +"\n"+
	            "void func1(int flag)"                                                 +"\n"+
	            "{"                                                                    +"\n"+
	            "	char *ptr;"                                                          +"\n"+
	            ""                                                                     +"\n"+
	            "	ptr = func2(flag);"                                                  +"\n"+
	            "	*ptr = 3;"                                                           +"\n"+
	            "	return; //DEFECT"                                                    +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "char* func2(int flag)"                                                +"\n"+
	            "{"                                                                    +"\n"+
	            "	char *ptr = NULL;"                                                   +"\n"+
	            ""                                                                     +"\n"+
	            "	if (flag > 0) {"                                                     +"\n"+
	            "		ptr = (char*)malloc(sizeof(char));"                                 +"\n"+
	            "	} else {"                                                            +"\n"+
	            "		ptr = func3();"                                                     +"\n"+
	            "	}"                                                                   +"\n"+
	            ""                                                                     +"\n"+
	            "	return ptr;"                                                         +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "char* func3()"                                                        +"\n"+
	            "{"                                                                    +"\n"+
	            "	char *ptr;"                                                          +"\n"+
	            ""                                                                     +"\n"+
	            "	ptr = (char*)malloc(sizeof(char));"                                  +"\n"+
	            "	return ptr;"                                                         +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
//	            "MLF_PRE"
	            "MLF"
	            ,
	            },

/////////////////  17   ///////////////////	
	           //qian:result:MLF 
	            {
	            "#include <stdlib.h>"                                                  +"\n"+
	            ""                                                                     +"\n"+
	            "char g_val = 'a';"                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "void func2(int, char*, char*);"                                       +"\n"+
	            "char* func3(char*, char*);"                                           +"\n"+
	            ""                                                                     +"\n"+
	            "void func1(int flag)"                                                 +"\n"+
	            "{"                                                                    +"\n"+
	            "	char *ptr1, *ptr2;"                                                  +"\n"+
	            ""                                                                     +"\n"+
	            "	ptr1 = (char*)malloc(sizeof(char));"                                 +"\n"+
	            "	ptr2 = (char*)malloc(sizeof(char));"                                 +"\n"+
	            "	func2(flag, ptr1, ptr2);"                                            +"\n"+
	            "} //DEFECT"                                                           +"\n"+
	            ""                                                                     +"\n"+
	            "void func2(int flag, char *ptr1, char *ptr2)"                         +"\n"+
	            "{"                                                                    +"\n"+
	            "	if (flag > 0) {"                                                     +"\n"+
	            "		*ptr1 = 3;"                                                         +"\n"+
	            "		*ptr2 = g_val;"                                                     +"\n"+
	            "		func3(ptr1, ptr2);"                                                 +"\n"+
	            "	} else {"                                                            +"\n"+
	            "		*ptr1 = g_val;"                                                     +"\n"+
	            "		*ptr2 = 5;"                                                         +"\n"+
	            "		func3(ptr1, ptr2);"                                                 +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "char* func3(char *ptr1, char *ptr2)"                                  +"\n"+
	            "{"                                                                    +"\n"+
	            "	if (ptr1) {"                                                         +"\n"+
	            "		free(ptr1);"                                                        +"\n"+
	            "	}"                                                                   +"\n"+
	            "	return ptr2;"                                                        +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
//	            "MLF_PRE"
	            "MLF"
	            ,
	            },
/////////////////  18   ///////////////////	
	            //qian 我认为应该是报告MLF 但是目前报告OK 正在修改  对if(ptr == null)return 处理错误
	            {
	            "#include <stdlib.h>"                                                  +"\n"+
	            ""                                                                     +"\n"+
	            "char* func2(int);"                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "void func1(int flag, int size)"                                       +"\n"+
	            "{"                                                                    +"\n"+
	            "	char *ptr;"                                                          +"\n"+
	            ""                                                                     +"\n"+
	            "	ptr = func2(size);"                                                  +"\n"+
	            "	if (ptr == NULL)"                                                    +"\n"+
	            "		return;"                                                            +"\n"+
	            ""                                                                     +"\n"+
	            "	if (flag < 0) {"                                                     +"\n"+
	            "		ptr = NULL; //DEFECT"                                               +"\n"+
	            "		return; "                                                           +"\n"+
	            "	} else {"                                                            +"\n"+
	            "		*ptr = 3;"                                                          +"\n"+
	            "	}"                                                                   +"\n"+
	            ""                                                                     +"\n"+
	            "	free(ptr);"                                                          +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "char* func2(int size)"                                                +"\n"+
	            "{"                                                                    +"\n"+
	            "	char *ptr = NULL;"                                                   +"\n"+
	            ""                                                                     +"\n"+
	            "	ptr = (char*)malloc(size*sizeof(char));"                             +"\n"+
	            "	return ptr;"                                                         +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
//	            "MLF_PRE"
	            "MLF"
	            ,
	            },
/////////////////  19   ///////////////////	
	            //qian:result:MLF
	            {
	            "#include <stdlib.h>"                                                  +"\n"+
	            ""                                                                     +"\n"+
	            "char* func2(int);"                                                    +"\n"+
	            "void func_del(char*);"                                                +"\n"+
	            ""                                                                     +"\n"+
	            "void func1(int flag, int size)"                                       +"\n"+
	            "{"                                                                    +"\n"+
	            "	char *ptr;"                                                          +"\n"+
	            ""                                                                     +"\n"+
	            "	ptr = func2(size);"                                                  +"\n"+
	            "	*ptr = 3;"                                                           +"\n"+
	            "	ptr = (char*)malloc(sizeof(char)); //DEFECT"                         +"\n"+
	            "	func_del(ptr);"                                                      +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "char* func2(int size)"                                                +"\n"+
	            "{"                                                                    +"\n"+
	            "	char *ptr = NULL;"                                                   +"\n"+
	            ""                                                                     +"\n"+
	            "	ptr = (char*)malloc(size*sizeof(char));"                             +"\n"+
	            "	return ptr;"                                                         +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "void func_del(char *ptr)"                                             +"\n"+
	            "{"                                                                    +"\n"+
	            "	free(ptr);"                                                          +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
//	            "MLF_PRE"
	            "MLF"
	            ,
	            },
/////////////////  20   ///////////////////	
	            //result:OK
	            {
	            "#include <stdlib.h>"                                                  +"\n"+
	            ""                                                                     +"\n"+
	            "char *g_ptr1 = NULL;"                                                 +"\n"+
	            "char *g_ptr2 = NULL;"                                                 +"\n"+
	            ""                                                                     +"\n"+
	            "void func2();"                                                        +"\n"+
	            "void func3();"                                                        +"\n"+
	            ""                                                                     +"\n"+
	            "void func1()"                                                         +"\n"+
	            "{"                                                                    +"\n"+
	            "	g_ptr1 = (char*)malloc(sizeof(char));"                               +"\n"+
	            "	g_ptr2 = (char*)malloc(sizeof(char));"                               +"\n"+
	            "	func2();"                                                            +"\n"+
	            "	func3();"                                                            +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "void func2()"                                                         +"\n"+
	            "{"                                                                    +"\n"+
	            "	char *temp;"                                                         +"\n"+
	            ""                                                                     +"\n"+
	            "	temp = g_ptr1;"                                                      +"\n"+
	            "	g_ptr1 = g_ptr2;"                                                    +"\n"+
	            "	g_ptr2 = temp;"                                                      +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "void func3()"                                                         +"\n"+
	            "{"                                                                    +"\n"+
	            "	if (g_ptr1)"                                                         +"\n"+
	            "		free(g_ptr1);"                                                      +"\n"+
	            ""                                                                     +"\n"+
	            "	free(g_ptr2);"                                                       +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "OK"
	            ,
	            },
/////////////////  21   ///////////////////	
	            //qian 我认为应该是报告MLF，但是目前报告OK，正在修改
	            {
	            "#include <stdlib.h>"                                                  +"\n"+
	            ""                                                                     +"\n"+
	            "void func2(int, char**);"                                             +"\n"+
	            "char* func3();"                                                       +"\n"+
	            ""                                                                     +"\n"+
	            "void func1(int flag)"                                                 +"\n"+
	            "{"                                                                    +"\n"+
	            "	char *ptr;"                                                          +"\n"+
	            ""                                                                     +"\n"+
	            "	func2(flag, &ptr);"                                                  +"\n"+
	            "	return; //DEFECT"                                                    +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "void func2(int flag, char **ptr)"                                     +"\n"+
	            "{"                                                                    +"\n"+
	            "	if (flag) {"                                                         +"\n"+
	            "		*ptr = (char*)malloc(sizeof(char));"                                +"\n"+
	            "	} else {"                                                            +"\n"+
	            "		*ptr = func3();"                                                    +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "char* func3()"                                                        +"\n"+
	            "{"                                                                    +"\n"+
	            "	char *ptr;"                                                          +"\n"+
	            ""                                                                     +"\n"+
	            "	ptr = (char*)malloc(sizeof(char));;"                                 +"\n"+
	            "	return ptr;"                                                         +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
//	            "MLF_PRE"
	            "MLF"
	            ,
	            },
/////////////////  22   ///////////////////	
	            {
	            "#include <stdlib.h>"                                                  +"\n"+
	            ""                                                                     +"\n"+
	            "void func2(int, int, char**);"                                        +"\n"+
	            "char* func3();"                                                       +"\n"+
	            ""                                                                     +"\n"+
	            "void func1(int flag)"                                                 +"\n"+
	            "{"                                                                    +"\n"+
	            "	char *ptr;"                                                          +"\n"+
	            ""                                                                     +"\n"+
	            "	func2(flag, 0, &ptr);"                                               +"\n"+
	            "	ptr = (char*)malloc(sizeof(char)); //DEFECT"                         +"\n"+
	            "	return;"                                                             +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "void func2(int flag, int n, char **ptr)"                              +"\n"+
	            "{"                                                                    +"\n"+
	            "	if (flag) {"                                                         +"\n"+
	            "		*ptr = (char*)malloc(sizeof(char));"                                +"\n"+
	            "	} else {"                                                            +"\n"+
	            "		*ptr = func3();"                                                    +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "char* func3()"                                                        +"\n"+
	            "{"                                                                    +"\n"+
	            "	char *ptr;"                                                          +"\n"+
	            ""                                                                     +"\n"+
	            "	ptr = (char*)malloc(sizeof(char));"                                  +"\n"+
	            "	return ptr;"                                                         +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
//	            "MLF_PRE"
	            "MLF"
	            ,
	            },
/////////////////  23   ///////////////////	
	            //20100726qian  我认为应该是报告MLF 
	            {
	            "#include <stdlib.h>"                                                  +"\n"+
	            ""                                                                     +"\n"+
	            "void func2(int, int, char**);"                                        +"\n"+
	            "char* func3();"                                                       +"\n"+
	            ""                                                                     +"\n"+
	            "void func1(int flag)"                                                 +"\n"+
	            "{"                                                                    +"\n"+
	            "	char *ptr;"                                                          +"\n"+
	            ""                                                                     +"\n"+
	            "	func2(&ptr, flag, 0);"                                               +"\n"+
	            "	if (ptr == NULL) {"                                                  +"\n"+
	            "		return; //FP"                                                       +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "void func2(char **ptr, int flag, int n)"                              +"\n"+
	            "{"                                                                    +"\n"+
	            "	if (flag) {"                                                         +"\n"+
	            "		*ptr = (char*)malloc(sizeof(char));"                                +"\n"+
	            "	} else {"                                                            +"\n"+
	            "		*ptr = func3();"                                                    +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "char* func3()"                                                        +"\n"+
	            "{"                                                                    +"\n"+
	            "	char *ptr;"                                                          +"\n"+
	            ""                                                                     +"\n"+
	            "	ptr = (char*)malloc(sizeof(char));"                                  +"\n"+
	            "	return ptr;"                                                         +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	//            "OK"
	            "MLF"
	            ,
	            },
/////////////////  24   ///////////////////	
	            //qian:result:OK
	            {
	            "#include <stdlib.h>"                                                  +"\n"+
	            ""                                                                     +"\n"+
	            "void func2(int, int, char**);"                                        +"\n"+
	            "char* func3();"                                                       +"\n"+
	            ""                                                                     +"\n"+
	            "int func1(int flag)"                                                  +"\n"+
	            "{"                                                                    +"\n"+
	            "	char *ptr;"                                                          +"\n"+
	            ""                                                                     +"\n"+
	            "	func2(&ptr, flag, 0);"                                               +"\n"+
	            "    "                                                                 +"\n"+
	            "    return 1; //DEFECT"                                               +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "void func2(char **ptr, int flag, int n)"                              +"\n"+
	            "{"                                                                    +"\n"+
	            "	if (flag) {"                                                         +"\n"+
	            "		*ptr = (char*)malloc(sizeof(char));"                                +"\n"+
	            "	} else {"                                                            +"\n"+
	            "		*ptr = func3();"                                                    +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "char* func3()"                                                        +"\n"+
	            "{"                                                                    +"\n"+
	            "	char *ptr;"                                                          +"\n"+
	            ""                                                                     +"\n"+
	            "	ptr = (char*)malloc(sizeof(char));"                                  +"\n"+
	            "	return ptr;"                                                         +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
//	            "MLF_PRE"
	            "MLF"
	            ,
	            },
/////////////////  25   ///////////////////	
	            //qian:result:OK
	            //之前头文件写错了
	            {
	            //"#include <assert.h>"                                                  +"\n"+
	            //"#include <stdio.h.h>"                                                  +"\n"+
	            "#include <stdlib.h>"                                                   +"\n"+
	            ""                                                                     +"\n"+
	            "void zk_mlf_2_f1(int flag,char *p)"                                   +"\n"+
	            "{   "                                                                 +"\n"+
	            "     if(flag)"                                                        +"\n"+
	            "         free(p);"                                                    +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "void zk_mlf_2_f2(int flag)"                                           +"\n"+
	            "{"                                                                    +"\n"+
	            "	char *buf = (char*)malloc(10*sizeof(char));"                         +"\n"+
	            ""                                                                     +"\n"+
	            "	zk_mlf_2_f1(flag,buf); //DEFECT"                                     +"\n"+
	            ""                                                                     +"\n"+
	            "	return;"                                                             +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
//	            "MLF_PRE"
	            "MLF"
	            ,
	            },

		});
	}
}
