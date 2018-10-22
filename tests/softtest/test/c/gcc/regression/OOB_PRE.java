package softtest.test.c.gcc.regression;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.io.ByteArrayInputStream;
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
public class OOB_PRE{
	private String source = null;
	private String compiletype=null;
	private String result = null;
	private static final String fsmPath="softtest/rules/gcc/fault/OOB_PRE-0.1.xml";
	FSMAnalysisVisitor fsmAnalysis; 
	private FSMControlFlowData cfData;
	
	static Pretreatment pre=new Pretreatment();
	static LibManager libManager = LibManager.getInstance();
	static InterContext interContext = InterContext.getInstance();
	static int testcaseNum=0;
	String temp;//预处理后的中间文件
	
	public OOB_PRE(String source,String compiletype, String result)
	{
		this.source=source;	
		this.compiletype=compiletype;
		this.result = result;
	}

	@BeforeClass
	public static void setUpBase()
	{
		//根据待测试模式XML文件路径初始化自动机列表
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		
		CAnalysis.deleteAndCreateTemp(Config.PRETREAT_DIR);
		pre.setPlatform(PlatformType.GCC);
		String INCLUDE = System.getenv("GCCINC");
		if(INCLUDE==null){
			throw new RuntimeException("System environment variable \"GCCINC\" error!");
		}
		String[] Inctemp = INCLUDE.split(";");
		//将GCCINC中的头文件目录，自动识别为头文件目录
		List<String> include = new ArrayList<String>();
		for(int i = 0;i<Inctemp.length;i++){
			Pretreatment.systemInc.add(Inctemp[i]);
			include.add(Inctemp[i]);
		}
		pre.setInclude(include);
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
		
		//将测试用例中的代码行，写到temp中形成.c源文件；
		String tempName="testcase_"+ (testcaseNum++) +".c";
		File tempFile=new File(Config.PRETREAT_DIR +"\\"+ tempName);
		if (Config.DELETE_PRETREAT_FILES) {
			tempFile.deleteOnExit();
		}
		FileWriter fw;
		try {
			fw = new FileWriter(tempFile);
			fw.write(source);
			fw.flush();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		temp=pre.pretreat(tempFile.getAbsolutePath(),  pre.getInclude(), new ArrayList<String>());
		
	}

	@After
	public void shutdown() {
		
	}

	@Test
	public void test() {
		try {
			CParser.setType("gcc");
			CParser parser_gcc;
			parser_gcc = CParser.getParser(new CCharStream(new FileInputStream(temp)));
			CParser.setType("keil");
			CParser parser_keil = CParser.getParser(new CCharStream(new FileInputStream(temp)));
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
				pre.setPlatform(PlatformType.GCC);
				analysis(gcc_astroot);
				
				CParser.setType("keil");
				try {
					keil_astroot= parser_keil.TranslationUnit();
				} catch (ParseException e) {
					e.printStackTrace();
					fail("parse error");
				}
				pre.setPlatform(PlatformType.KEIL);
				analysis(keil_astroot);
			}
		} catch (FileNotFoundException e1) {
			e1.printStackTrace();
		}
	}
	
	 @Parameters
	 public static Collection<Object[]> testcaseAndResults()
	 {
		 return Arrays.asList(new Object[][] {
	/////////////////  0   ///////////////////	
		//避免区间运算错引起的【-inf，*】【*，inf】的误报，屏蔽此类区间的检查，故用例0.1目前的检查结果是ok
		            {
		            "#define MAX 5"                                                        +"\n"+
		            ""                                                                     +"\n"+
		            "int g_array[MAX];"                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int);"                                                     +"\n"+
		            "void func3(int, int, int);"                                           +"\n"+
		            ""                                                                     +"\n"+
		            "void func1()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	int i;"                                                              +"\n"+
		            ""                                                                     +"\n"+
		            "	i = MAX;"                                                            +"\n"+
		            "	func2(i); "                                                          +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int var)"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (var < MAX) {"                                                    +"\n"+
		            "		g_array[var] = var;"                                                +"\n"+
		            "	} else {"                                                            +"\n"+
		            "		func3(0, 0, var);//DEFECT"                                          +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func3(int n, int m, int var)"                                    +"\n"+
		            "{"                                                                    +"\n"+
		            "	g_array[var] = var;"                                                 +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB_PRE"
		            ,
		            },
	/////////////////  1   ///////////////////	
		            {
		            "#define MAX 5"                                                        +"\n"+
		            ""                                                                     +"\n"+
		            "int g_array[MAX][MAX];"                                               +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int);"                                                     +"\n"+
		            "void func3(int, int, int);"                                           +"\n"+
		            ""                                                                     +"\n"+
		            "void func1()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	int i;"                                                              +"\n"+
		            ""                                                                     +"\n"+
		            "	i = MAX;"                                                            +"\n"+
		            "	func2(i); //"                                                        +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int var)"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (var < MAX) {"                                                    +"\n"+
		            "		g_array[0][var] = var;"                                             +"\n"+
		            "	} else {"                                                            +"\n"+
		            "		func3(0, var, 0);//DEFECT"                                          +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func3(int n, int var, int m)"                                    +"\n"+
		            "{"                                                                    +"\n"+
		            "	g_array[var][var] = var;"                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB_PRE"
		            ,
		            },
	/////////////////  2   ///////////////////	
		            {
		            "#define MAX 5"                                                        +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int);"                                                     +"\n"+
		            "void func3(int, int, int);"                                           +"\n"+
		            "void func4(int, int, int);"                                           +"\n"+
		            ""                                                                     +"\n"+
		            "void func1(int var)"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	func2(var); //FP"                                                    +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int var)"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	func3(0, var, 0);"                                                   +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func3(int n, int var, int m)"                                    +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (var < 0 || var >= MAX) {"                                        +"\n"+
		            "		return;"                                                            +"\n"+
		            "	} else {"                                                            +"\n"+
		            "		func4(0, 0, var);"                                                  +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func4(int n, int m, int var)"                                    +"\n"+
		            "{"                                                                    +"\n"+
		            "	int array[MAX];"                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "	array[var] = var;"                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
/////////////////  3   ///////////////////	
		            {
		            "void f(int v){"                                                       +"\n"+
		            "   int a[10];"                                                        +"\n"+
		            "   int j=a[v];"                                                       +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f1(){"                                                           +"\n"+
		            ""                                                                     +"\n"+
		            "   f(55); //DEFECT"                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB_PRE"
		            ,
		            },
	/////////////////  4有关于复杂表达式  ///////////////////	
		            {
		            "#define MAX 5"                                                        +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int);"                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "void func1()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	int i;"                                                              +"\n"+
		            ""                                                                     +"\n"+
		            "	i = MAX;"                                                            +"\n"+
		            "	func2(i); //DEFECT"                                                  +"\n"+
		            "    func3(i);//DEFECT"                                                +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "void func3(int var)"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "   struct pb{"                                                        +"\n"+
		            "	   int g_array[MAX];"                                                +"\n"+
		            "	};"                                                                  +"\n"+
		            "	struct pc{"                                                          +"\n"+
		            "	   struct pb* B;"                                                    +"\n"+
		            "	}C;"                                                                 +"\n"+
		            ""                                                                     +"\n"+
		            "	C.B->g_array[var] = var;"                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int var)"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "   struct pb{"                                                        +"\n"+
		            "	   int g_array[MAX];"                                                +"\n"+
		            "	}A;"                                                                 +"\n"+
		            "    A.g_array[var] = var;"                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB_PRE"
		            ,
		            },
	/////////////////  5   ///////////////////	
		            {
		            "typedef struct{"                                                      +"\n"+
		            "   int a;"                                                            +"\n"+
		            "}S;"                                                                  +"\n"+
		            "S s;"                                                                 +"\n"+
		            "void f(){"                                                            +"\n"+
		            "    int a[12];"                                                       +"\n"+
		            "    a[s.a]=11;"                                                       +"\n"+
		            "}"                                                                    +"\n"+
		            "void f1(){"                                                           +"\n"+
		            "    f();"                                                             +"\n"+
		            "}"                                                                    +"\n"+
		            "void f3(){"                                                           +"\n"+
		            "    s.a=222;"                                                         +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2(){"                                                           +"\n"+
		            "   f3();"                                                             +"\n"+
		            "   f1();    "                                                         +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB_PRE"
		            ,
		            },
	/////////////////  6   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "int f(){"                                                             +"\n"+
		            "   return 10;"                                                        +"\n"+
		            "}"                                                                    +"\n"+
		            "void f1(int i){"                                                      +"\n"+
		            "   int a[5];"                                                         +"\n"+
		            "   a[i]=1;"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2(){"                                                           +"\n"+
		            "   f1(f()); "                                                         +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB_PRE"
		            ,
		            },

		            

		 });
	 }
}
