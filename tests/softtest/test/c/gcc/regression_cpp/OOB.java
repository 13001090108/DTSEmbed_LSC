package softtest.test.c.gcc.regression_cpp;

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
public class OOB {
	private String source = null;
	private String compiletype=null;
	private String result = null;
	private static final String fsmPath="softtest/rules/gcc/fault/OOB-0.1.xml";
	FSMAnalysisVisitor fsmAnalysis; 
	private FSMControlFlowData cfData;

	static Pretreatment pre=new Pretreatment();
	static InterContext interContext = InterContext.getInstance();
	static int testcaseNum=0;
	String temp;//预处理后的中间文件

	public OOB(String source,String compiletype, String result)
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

		//根据当前检测的测试用例，载入相关的库函数摘要

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
				//////////////////////////0//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                            +"\n"+
					"#include <string.h>"                                                            +"\n"+
					"#include <stdio.h>"                                                            +"\n"+
					"int c[5];"                                                            +"\n"+
							"int test1 () {"                                                       +"\n"+
							"  int a[] = {1,2,3,4,2},b[5];"                                             +"\n"+
							"  a[6] = 1;  //DEFECT,OOB,a"                                          +"\n"+
							"  a[5] = 1;	 //DEFECT,OOB,a"                                          +"\n"+
							""                                                          +"\n"+
							"  b[6]; //DEFECT,OOB,b"                                               +"\n"+
							"  c[6];  //DEFECT,OOB,c"                                              +"\n"+
							"  return 0;"                                                          +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int test3(int argc, char *argv[])"                                    +"\n"+
							"{"                                                                    +"\n"+
							"  static   char buf[10] = \"\";"                                        +"\n"+
							""                                                                     +"\n"+
							""                                                                     +"\n"+
							"  /*  OK  */"                                                         +"\n"+
							"  buf[9] = 'A';   //FP,OOB"                                           +"\n"+
							""                                                                     +"\n"+
							""                                                                     +"\n"+
							"  return 0;"                                                          +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},
				//////////////////////////1//////////////////////////////////////////////
				{
					"#include <string.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"void test1(){"                                                        +"\n"+
							"	char arr[100];"                                                      +"\n"+
							"	int l=strlen(arr);"                                                  +"\n"+
							"	if(l>1 && arr[l-2]==2)"                                              +"\n"+
							"		arr[l-2]=0;  //FP, OOB"                                             +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"//*********************"                                              +"\n"+
							"int numlength=100;"                                                   +"\n"+
							"int arr2[numlength];"                                                 +"\n"+
							"void test2(int index){"                                               +"\n"+
							"	if(index>=numlength || index<0)"                                     +"\n"+
							"		return;"                                                            +"\n"+
							"	arr2[index]=2; //FP, OOB"                                            +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void test3(){"                                                        +"\n"+
							"	char arr[10];"                                                       +"\n"+
							"	int j=0;"                                                            +"\n"+
							"	for(j=-1+strlen(arr);j>=0;--j){"                                     +"\n"+
							"		arr[j]=0;	 //FP, OOB"                                               +"\n"+
							"	}"                                                                   +"\n"+
							"}"                                                                    +"\n"+
							"int ab[3]={1,2,3};"                                                   +"\n"+
							"void test4(int i){"                                                   +"\n"+
							"	int result=0;"                                                       +"\n"+
							"	if(i<0)"                                                             +"\n"+
							"		return;"                                                            +"\n"+
							"	if(i<sizeof(ab)/sizeof(ab[0]))"                                      +"\n"+
							"	 result=ab[i];   //FP, OOB"                                          +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"#define  MAX 100"                                                     +"\n"+
							"struct str{"                                                          +"\n"+
							"	char*s;"                                                             +"\n"+
							"	char a[MAX];"                                                        +"\n"+
							"};"                                                                   +"\n"+
							""                                                                     +"\n"+
							"void test5(int i){"                                                   +"\n"+
							"      int a[12];"                                                     +"\n"+
							"      a[13]=1;//DEFECT,OOB,a"                                         +"\n"+
							"  	  struct str s;"                                                          +"\n"+
							"	  if(i<=MAX){"                                                       +"\n"+
							"		  s.a[i]=1;//DEFECT,OOB,a"                                          +"\n"+
							"	  }"                                                                 +"\n"+
							""                                                                     +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},
				//////////////////////////2//////////////////////////////////////////////
				{
					"int test1 () {"                                                       +"\n"+
							"  int a[4] ;"                                                         +"\n"+
							"  int i = 4;"                                                         +"\n"+
							"  a[i] = 1;	//DEFECT,OOB,a"                                           +"\n"+
							"  return 0;"                                                          +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void test2 () {"                                                      +"\n"+
							"  int a[4] ;"                                                         +"\n"+
							"  int i = 4;"                                                         +"\n"+
							"  a[i] = 1;	 //DEFECT,OOB,a"                                          +"\n"+
							"  return 0;"                                                          +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"#define MAX 10"                                                       +"\n"+
							""                                                                     +"\n"+
							"void test3(){"                                                        +"\n"+
							"	int a[MAX];"                                                         +"\n"+
							"	int *p=a;"                                                           +"\n"+
							"	p[MAX]=1;//DEFECT,OOB,p"                                             +"\n"+
							"	a[MAX]=1;//DEFECT,OOB,a"                                             +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},
				//////////////////////////3//////////////////////////////////////////////
				{
					"int c[3][3];"                                                         +"\n"+
							"void f(){"                                                            +"\n"+
							"  int b[3][3];"                                                       +"\n"+
							"  b[1][1]=0;"                                                         +"\n"+
							"  b[1][2]=0;"                                                         +"\n"+
							"  b[3][1]=0;  //DEFECT,OOB,b"                                         +"\n"+
							"  b[2][3]=0;  //DEFECT,OOB,b"                                         +"\n"+
							"  b[2][2]=0;  //FP,OOB"                                               +"\n"+
							"  c[1][3]=0;  //DEFECT,OOB,c"                                         +"\n"+
							"  c[3][1]=0;  //DEFECT,OOB,c"                                         +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},
				//////////////////////////4//////////////////////////////////////////////
				{
					"int i;"                                                               +"\n"+
							"void f(){"                                                            +"\n"+
							"  int b[][3]={{1,2,4},{1,2,3},{1,2,3}};"                              +"\n"+
							"  b[1][1]=0;"                                                         +"\n"+
							"  b[1][2]=0;"                                                         +"\n"+
							"  b[3][1]=0; //DEFECT,OOB,b"                                          +"\n"+
							"  b[2][3]=0; //DEFECT,OOB,b"                                          +"\n"+
							"  b[2][2]=0;  //FP,OOB"                                               +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},
				//////////////////////////5////////////////////////////////////////	
				{
					"int main()"                                                           +"\n"+
							"{"                                                                    +"\n"+
							"	int a[10]={0,1,2,3,4,5,6,7,8,9};"                                    +"\n"+
							"	a[10] = 1;  //DEFECT,OOB,a"                                          +"\n"+
							"	int b[10]={0};"                                                      +"\n"+
							"	int c[]={1,2,3,4};"                                                  +"\n"+
							"	int d[2][3]={{2,3,4},{4,5,6}};"                                      +"\n"+
							"	d[2][3] = 1;  //DEFECT,OOB,d"                                        +"\n"+
							"	char f[3]={'a','b','c'};"                                            +"\n"+
							"	char g[3]={\"ac\"};"                                                   +"\n"+
							"	g[3] = 'c';  //DEFECT,OOB,g"                                         +"\n"+
							"	return 0;"                                                           +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							""                                                                     +"\n"+
							"int func1(int a) {"                                                   +"\n"+
							"	int array[4];"                                                       +"\n"+
							"	if (a > 4 || a < 0) {"                                               +"\n"+
							"		return 0;"                                                          +"\n"+
							"	}"                                                                   +"\n"+
							"	array[a] = 1;  //DEFECT,OOB,array"                                   +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int func2(int a) {"                                                   +"\n"+
							"	int array[4];"                                                       +"\n"+
							"	if (a>=0 && a<=4) {"                                                 +"\n"+
							"		array[a] = 1;  //DEFECT,OOB,array"                                  +"\n"+
							"		"                                                                   +"\n"+
							"	}"                                                                   +"\n"+
							"	return 0;"                                                           +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},
				//////////////////////////6//////////////////////////////////////////////
				{
					"typedef struct _Test {"                                               +"\n"+
							"	int a[2];"                                                           +"\n"+
							"} Test;"                                                              +"\n"+
							""                                                                     +"\n"+
							"int test1()"                                                          +"\n"+
							"{"                                                                    +"\n"+
							"	Test st[2] = {0};"                                                   +"\n"+
							"	st[0].a[0] = 1;"                                                     +"\n"+
							"	st[0].a[1] = 1;"                                                     +"\n"+
							"	st[2].a[0] = 1;  //DEFECT,OOB,st"                                    +"\n"+
							"	st[2].a[2] = 1;  //DEFECT,OOB,st"                                    +"\n"+
							"	return 0;"                                                           +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int test2()"                                                          +"\n"+
							"{"                                                                    +"\n"+
							"	int a[2][2] = {0};"                                                  +"\n"+
							"	a[0][2] = 1;  //DEFECT,OOB,a"                                        +"\n"+
							"	a[2][0] = 1;  //DEFECT,OOB,a"                                        +"\n"+
							"	return 0;"                                                           +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int test3()"                                                          +"\n"+
							"{"                                                                    +"\n"+
							"	int arr[20];"                                                        +"\n"+
							"	int n;"                                                              +"\n"+
							"	n = arr[sizeof(arr)-1];   //DEFECT,OOB,arr"                          +"\n"+
							"	n = arr[sizeof(arr)/sizeof(int)-1];"                                 +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},
				
				
				/////////////////////////7/////////////////////////////////////////////
				{
					"#include <string.h>"                                                  +"\n"+
							"typedef struct"                                                       +"\n"+
							"{"                                                                    +"\n"+
							"  char buf[10];"                                                      +"\n"+
							"} my_struct;"                                                         +"\n"+
							""                                                                     +"\n"+
							"int func1()"                                                          +"\n"+
							"{"                                                                    +"\n"+
							"  my_struct s;"                                                       +"\n"+
							""                                                                     +"\n"+
							""                                                                     +"\n"+
							"  /*  BAD  */"                                                        +"\n"+
							"  s.buf[4105] = 'A';  //DEFECT,OOB,buf"                               +"\n"+
							"	s.buf[10] = 'A';  //DEFECT,OOB,buf"                                  +"\n"+
							"	s.buf[1] = 'A';"                                                     +"\n"+
							"  return 0;"                                                          +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"typedef union"                                                        +"\n"+
							"{"                                                                    +"\n"+
							"  char buf[10];"                                                      +"\n"+
							"  int intval;"                                                        +"\n"+
							"} my_union;"                                                          +"\n"+
							""                                                                     +"\n"+
							""                                                                     +"\n"+
							"int func2()"                                                          +"\n"+
							"{"                                                                    +"\n"+
							"  my_union u;"                                                        +"\n"+
							""                                                                     +"\n"+
							"  /*  BAD  */"                                                        +"\n"+
							"  u.buf[4105] = 'A';  //DEFECT,OOB,buf"                               +"\n"+
							"	u.buf[10] = 'A';   //DEFECT,OOB,buf"                                 +"\n"+
							"	u.buf[1] = 'A';"                                                     +"\n"+
							"  return 0;"                                                          +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"typedef struct"                                                       +"\n"+
							"{"                                                                    +"\n"+
							"  char buf[10];"                                                      +"\n"+
							"} my_struct;"                                                         +"\n"+
							""                                                                     +"\n"+
							"int func3()"                                                          +"\n"+
							"{"                                                                    +"\n"+
							"  my_struct array_buf[5];"                                            +"\n"+
							""                                                                     +"\n"+
							""                                                                     +"\n"+
							"  /*  BAD  */"                                                        +"\n"+
							"  array_buf[4].buf[4105] = 'A';   //DEFECT,OOB,buf"                   +"\n"+
							"	array_buf[5].buf[4105] = 'A';  //DEFECT,OOB,buf"                     +"\n"+
							"	array_buf[5].buf[5] = 'A';  //DEFECT,OOB,array_buf"                  +"\n"+
							"	array_buf[4].buf[5] = 'A';"                                          +"\n"+
							"  return 0;"                                                          +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void test1(){"                                                        +"\n"+
							"	int arr[100];"                                                       +"\n"+
							"	int l=strlen(arr);"                                                  +"\n"+
							"	if(l>1&&l<100)"                                                      +"\n"+
							"		arr[l-2]=0;   //FP,OOB"                                             +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							""                                                                     +"\n"+
							"int numlength=100;"                                                   +"\n"+
							"int arr2[numlength];"                                                 +"\n"+
							"void test2(int index){"                                               +"\n"+
							"	if(index>=numlength || index<0)"                                     +"\n"+
							"		return;"                                                            +"\n"+
							"	arr2[index]=2;  //FP,OOB"                                            +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void test3(){"                                                        +"\n"+
							"	char p[10];"                                                         +"\n"+
							"	int a;"                                                              +"\n"+
							"	a = strlen(p) - 2;;"                                                 +"\n"+
							"	if (a > 0) {"                                                        +"\n"+
							"		p[a] = 1; //FP,OOB"                                                 +"\n"+
							"	}"                                                                   +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void test4(){"                                                        +"\n"+
							"	char p[10];"                                                         +"\n"+
							"	int a;"                                                              +"\n"+
							"	a = strlen(p);"                                                      +"\n"+
							"	a = a - 2;"                                                          +"\n"+
							"	if (a > 0) {"                                                        +"\n"+
							"		p[a] = 1; //FP,OOB"                                                 +"\n"+
							"	}"                                                                   +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void test6(){"                                                        +"\n"+
							"	char arr[10];"                                                       +"\n"+
							"	int j=0;"                                                            +"\n"+
							"	for(j=-1+strlen(arr);j>=0;--j){"                                     +"\n"+
							"		arr[j]=0;	//FP,OOB"                                                 +"\n"+
							"	}"                                                                   +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},
				/////////////////////////8/////////////////////////////////////////////
				{
					"char *ghx_oob_1_f1()"                                                 +"\n"+
							"{"                                                                    +"\n"+
							"    char mm[200];"                                                    +"\n"+
							"	int cc;"                                                             +"\n"+
							"	char ff;"                                                            +"\n"+
							""                                                                     +"\n"+
							"	for (cc=0; cc<500; cc++)"                                            +"\n"+
							"	{"                                                                   +"\n"+
							"		ff=mm[cc]; //DEFECT"                                                +"\n"+
							"	}"                                                                   +"\n"+
							""                                                                     +"\n"+
							"	return 0;"                                                           +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},
				/////////////////////////9/////////////////////////////////////////////
				{
					"#define  m 100"                                                       +"\n"+
							"struct ghx_oob_2_sl"                                                  +"\n"+
							"{"                                                                    +"\n"+
							"	char*s;"                                                             +"\n"+
							"	char a[m];"                                                          +"\n"+
							"};"                                                                   +"\n"+
							""                                                                     +"\n"+
							"ghx_oob_2_f2(int i)"                                                  +"\n"+
							"{"                                                                    +"\n"+
							"      int a[12];"                                                     +"\n"+
							"      a[13]=1;"                                                       +"\n"+
							"  	  struct ghx_oob_2_sl s;"                                                 +"\n"+
							"	  if(i<=m){"                                                         +"\n"+
							"		  s.a[i]=1;//DEFECT"                                                +"\n"+
							"	  }"                                                                 +"\n"+
							"	  return 0;"                                                         +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},
				/////////////////////////10/////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"int a[100];"                                                          +"\n"+
							"void fun(){"                                                          +"\n"+
							"    int i,k=10;"                                                        +"\n"+
							"	for( i=0;i<20;i++)"                                               +"\n"+
							"		a[i*k]=0;"                                                          +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},
				/////////////////////////11/////////////////////////////////////////////
				{
					""                                                                     +"\n"+
							"void yxh_oob_f1()"                                                    +"\n"+
							"{"                                                                    +"\n"+
							"	char buf[4];"                                                        +"\n"+
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
				/////////////////////////12/////////////////////////////////////////////
				{
					""                                                                     +"\n"+
							"void yxh_oob_f1()"                                                    +"\n"+
							"{"                                                                    +"\n"+
							"	char buf[4];"                                                        +"\n"+
							"	int i = 1, j = 2;"                                                   +"\n"+
							"	"                                                                    +"\n"+
							"	(buf+1)[3] = 'c'; //DEFECT"                                          +"\n"+
							"	(buf+j)[i] = 'c';"                                                   +"\n"+
							"	"                                                                    +"\n"+
							"	char c = (buf+j)[j]; //DEFECT"                                       +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},
				/////////////////////////13/////////////////////////////////////////////
				{
					""                                                                     +"\n"+
							"void yxh_oob_f1()"                                                    +"\n"+
							"{"                                                                    +"\n"+
							"	char buf[13];"                                                       +"\n"+
							"	((int *)buf)[4] = 1; //DEFECT"                                       +"\n"+
							"	"                                                                    +"\n"+
							"	int arr[4];"                                                         +"\n"+
							"	((char *)arr)[15] = 'c';"                                            +"\n"+
							"	((char *)arr)[16] = 'c'; //DEFECT"                                   +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},
				/////////////////////////14/////////////////////////////////////////////
				{
					""                                                                     +"\n"+
							"void yxh_oob_5_f1()"                                                  +"\n"+
							"{"                                                                    +"\n"+
							"	int buf[4];"                                                         +"\n"+
							"	char *p = (char *)buf;"                                              +"\n"+
							"	p[15] = 'c';"                                                        +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				
				/////////////////////////15/////////////////////////////////////////////
				{
					"int f(int x1, int y1, int flag)"                                      +"\n"+
							"{"                                                                    +"\n"+
							"	int yes;"                                                            +"\n"+
							"	int kernel[8][8];"                                                   +"\n"+
							"	int temp=flag;"                                                      +"\n"+
							"	int x=0,y=0,i=0,j=0;"                                                +"\n"+
							"	if(x1<0 || x1>=8 || y1<0 || y1>=8)"                                  +"\n"+
							"		return 0;"                                                          +"\n"+
							"	"                                                                    +"\n"+
							"	x=x1;"                                                               +"\n"+
							"	"                                                                    +"\n"+
							"	yes=0;"                                                              +"\n"+
							"  	"                                                                  +"\n"+
							"	for(i=y1-1;i>=0;i--)"                                                +"\n"+
							"	{"                                                                   +"\n"+
							"		if(kernel[x][i]==0)"                                                +"\n"+
							"		{"                                                                  +"\n"+
							"			yes=0;"                                                            +"\n"+
							"			break;"                                                            +"\n"+
							"		}"                                                                  +"\n"+
							"		else if(kernel[x][i]==temp)"                                        +"\n"+
							"			break;"                                                            +"\n"+
							"		else"                                                               +"\n"+
							"			yes=1;"                                                            +"\n"+
							"	}"                                                                   +"\n"+
							"	if((i!=0-1) && (yes==1))"                                            +"\n"+
							"	{"                                                                   +"\n"+
							"		for(i++;i<y1;i++)"                                                  +"\n"+
							"		{"                                                                  +"\n"+
							"			kernel[x][i]=temp;//OOB, FP"                                       +"\n"+
							"		}"                                                                  +"\n"+
							"	}"                                                                   +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////////////16/////////////////////////////////////////////
				{
					"#include <stdio.h>"                                                   +"\n"+
							"void ghx_oob_10_f10()"                                                +"\n"+
							"{"                                                                    +"\n"+
							"char b[8];"                                                           +"\n"+
							"int a=1;"                                                             +"\n"+
							"int c=0;"                                                             +"\n"+
							"if(a>0)"                                                              +"\n"+
							"{"                                                                    +"\n"+
							"c++;"                                                                 +"\n"+
							"b[c]=0;//FP"                                                          +"\n"+
							"}"                                                                    +"\n"+
							"printf(\"%d\\n\",c);"                                                    +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////////////17/////////////////////////////////////////////
				{
					"void ghx_oob_11_f11(int a)"                                           +"\n"+
							"{"                                                                    +"\n"+
							"char b[15];"                                                          +"\n"+
							"int i,j=0;"                                                             +"\n"+
							"for( i=0;i<a;i++)"                                                 +"\n"+
							"{"                                                                    +"\n"+
							"b[j]=1;//FP"                                                          +"\n"+
							"}"                                                                    +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////////////18/////////////////////////////////////////////	
				{
					"int ghx_oob_12_f11()"                                                 +"\n"+
							"{"                                                                    +"\n"+
							"return 1;"                                                            +"\n"+
							"}"                                                                    +"\n"+
							"void ghx_oob_12_f12()"                                                +"\n"+
							"{"                                                                    +"\n"+
							"int m=ghx_oob_12_f11();"                                              +"\n"+
							"int n=(m&1),j;"                                                         +"\n"+
							"char c[15];"                                                          +"\n"+
							"for( j=0;j<n;j++)"                                                 +"\n"+
							"c[n-1-j]=0;//DEFECT"                                                  +"\n"+
							""                                                                     +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////////////19/////////////////////////////////////////////
				{
					"#include <string.h>"                                                  +"\n"+
							"#include <stdio.h>"                                                   +"\n"+
							"void main()"                                                          +"\n"+
							"{"                                                                    +"\n"+
							"char s[]=\"abc\";"                                                      +"\n"+
							"int a=strlen(s);"                                                     +"\n"+
							"s[a]=0;"                                                              +"\n"+
							"printf(\"%d\\n\",a);"                                                    +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////////////20/////////////////////////////////////////////
				{
					"void ghx_oob_14_f14(int b)"                                           +"\n"+
							"{"                                                                    +"\n"+
							"int a[4];"                                                            +"\n"+
							"if(b>0||b<3)"                                                         +"\n"+
							"{"                                                                    +"\n"+
							"a[b]=1;//DEFECT"                                                      +"\n"+
							"}"                                                                    +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},
				/////////////////////////21/////////////////////////////////////////////
				{
					"int ghx_oob_15_f15(int b)"                                            +"\n"+
							"{"                                                                    +"\n"+
							"int a[4];"                                                            +"\n"+
							"if(b>4||b<0)"                                                         +"\n"+
							"{return 0;}"                                                          +"\n"+
							"a[b]=1;//DEFECT"                                                      +"\n"+
							"return 1;"                                                            +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},
				/////////////////////////22/////////////////////////////////////////////
				{
					"#define  m 100"                                                       +"\n"+
							"struct ghx_oob_2_sl"                                                  +"\n"+
							"{"                                                                    +"\n"+
							"	char*s;"                                                             +"\n"+
							"	char a[m];"                                                          +"\n"+
							"};"                                                                   +"\n"+
							""                                                                     +"\n"+
							"ghx_oob_2_f2(int i)"                                                  +"\n"+
							"{"                                                                    +"\n"+
							"      int a[12];"                                                     +"\n"+
							"      a[13]=1;"                                                       +"\n"+
							"  	  struct ghx_oob_2_sl s;"                                                 +"\n"+
							"	  if(i<=m){"                                                         +"\n"+
							"		  s.a[i]=1;//DEFECT"                                                +"\n"+
							"	  }"                                                                 +"\n"+
							"	  return 0;"                                                         +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},
				/////////////////////////23/////////////////////////////////////////////
				{
					"void ghx_oob_3_f3 (int i) "                                           +"\n"+
							"{"                                                                    +"\n"+
							""                                                                     +"\n"+
							"  int a[4] = {1,2,3,4};"                                              +"\n"+
							"  if(i > 2)"                                                          +"\n"+
							"  {"                                                                  +"\n"+
							"     a[i] = 1;//DEFECT"                                               +"\n"+
							"  }"                                                                  +"\n"+
							"  else if(i> 0 && i < 3)"                                             +"\n"+
							"  {"                                                                  +"\n"+
							"     a[i] = 1;//FP"                                                   +"\n"+
							"  }"                                                                  +"\n"+
							"  else"                                                               +"\n"+
							"  {"                                                                  +"\n"+
							"     a[i] = 2;//DEFECT"                                               +"\n"+
							"  }"                                                                  +"\n"+
							"  return ;"                                                           +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},
				/////////////////////////24/////////////////////////////////////////////
				{
					"int ghx_oob_4_F4()"                                                   +"\n"+
							"{"                                                                    +"\n"+
							" int a[5]={2,3,5,7,9},i,k;"                                               +"\n"+
							" int to=0;"                                                           +"\n"+
							" for (i=0;i<5;i++)"                                               +"\n"+
							" {"                                                                   +"\n"+
							"  for(k=0;k<5-i;k++)"                                             +"\n"+
							"  {"                                                                  +"\n"+
							"   if(a[k]<a[k+1])//DEFECT"                                           +"\n"+
							"   {"                                                                 +"\n"+
							"       to=a[k];"                                                      +"\n"+
							"   }"                                                                 +"\n"+
							"  }"                                                                  +"\n"+
							" }"                                                                   +"\n"+
							""                                                                     +"\n"+
							"   return 0;"                                                         +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},
				
				/////////////////////////25/////////////////////////////////////////////
				{
					"#include <stdio.h>"                                                   +"\n"+
							"void ghx_oob_9_f9()"                                                  +"\n"+
							"{"                                                                    +"\n"+
							"char a[10];"                                                          +"\n"+
							"int m=0,w;"                                                             +"\n"+
							"for(w=0;w<20;w++)"                                                +"\n"+
							"{"                                                                    +"\n"+
							"a[m++]=1;"                                                            +"\n"+
							"}"                                                                    +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},
				/////////////////////////26/////////////////////////////////////////////
				{
					"#include <stdio.h>"                                                   +"\n"+
							"int ghx_oob_8_f8()"                                                   +"\n"+
							"{"                                                                    +"\n"+
							"char buffer[68];"                                                     +"\n"+
							"int b=4;"                                                             +"\n"+
							"int a=1;"                                                             +"\n"+
							"buffer[b]=1;"                                                         +"\n"+
							"b+=34;"                                                               +"\n"+
							"if(a)"                                                                +"\n"+
							"{"                                                                    +"\n"+
							" if(b)"                                                               +"\n"+
							"   b+=34;"                                                            +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"buffer[b]=2;//DEFECT"                                                 +"\n"+
							"return 0;"                                                            +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},
				
				
				/////////////////////////27/////////////////////////////////////////////
				//char buf[6] = {1, 2, 3, 4, 5, 0}; long l = strlen(buf);得到l的区间是[0,5]
				//      ------聂敏慧
				{
					"#include <string.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"void func1(int var)"                                                  +"\n"+
							"{"                                                                    +"\n"+
							"	char buf[6] = {1, 2, 3, 4, 5, 0};"                                   +"\n"+
							"   long l; "                                                                     +"\n"+
							"	if (buf[0]) {"                                                       +"\n"+
							"		l = strlen(buf);"                                              +"\n"+
							"		if (l > 1)"                                                         +"\n"+
							"			buf[l-2]++;"                                                       +"\n"+
							"		else if (buf[l-1] > 0)"                                             +"\n"+
							"			buf[l-1]++;"                                                       +"\n"+
							"	}"                                                                   +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},
				/////////////////////////28/////////////////////////////////////////////

				{
					"#define MAX 5"                                                        +"\n"+
							""                                                                     +"\n"+
							"void func1()"                                                         +"\n"+
							"{"                                                                    +"\n"+
							"	int i;"                                                              +"\n"+
							"	int buf[MAX] = {0,0,0,0,0};"                                         +"\n"+
							"	int tmp;"                                                            +"\n"+
							""                                                                     +"\n"+
							"	for (i = 0; i <= MAX; i++)"                                          +"\n"+
							"	{"                                                                   +"\n"+
							"		tmp = i == 0 ? 0 : buf[i-1]; //FP"                                  +"\n"+
							"	}"                                                                   +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},
				/////////////////////////29/////////////////////////////////////////////
				{
					"void f()"                                                             +"\n"+
							"{"                                                                    +"\n"+
							"     int i = 30, j;"                                                  +"\n"+
							"     int a[10] = {0};"                                                +"\n"+
							"     "                                                                +"\n"+
							"     j = i;"                                                          +"\n"+
							"     for (i=0; i<5; i++)"                                             +"\n"+
							"         j++;"                                                        +"\n"+
							""                                                                     +"\n"+
							"     a[i] = 100;//FP"                                                 +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////////////30/////////////////////////////////////////////
				{
					""                                                                     +"\n"+
							"void func1()"                                                         +"\n"+
							"{"                                                                    +"\n"+
							"	int buf[10];"                                                        +"\n"+
							"	int *ptr;"                                                           +"\n"+
							""                                                                     +"\n"+
							"	ptr = (int*)((int)(&buf[0]) & ~3);"                                  +"\n"+
							"	ptr[5] = 3; //FP"                                                    +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				
				/////////////////////////31/////////////////////////////////////////////	
				{
					"#define SIZE 10"                                                      +"\n"+
							""                                                                     +"\n"+
							"void func1()"                                                         +"\n"+
							"{"                                                                    +"\n"+
							"	int buf[SIZE];"                                                      +"\n"+
							"	int i;"                                                              +"\n"+
							""                                                                     +"\n"+
							"	for (i = 0; i <= SIZE - 2; i++) {"                                   +"\n"+
							"		;"                                                                  +"\n"+
							"	}"                                                                   +"\n"+
							""                                                                     +"\n"+
							"	buf[i] = i; //FP"                                                    +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////////////32/////////////////////////////////////////////
				{
					"  void foo()"                                                         +"\n"+
							"  {"                                                                  +"\n"+
							"      char a[8]; "                                                    +"\n"+
							"      ((int*)a)[5] = 0; //DEFECT"                                     +"\n"+
							"  }"                                                                  
							,
							"gcc"
							,
							"OOB"
							,
				},
				/////////////////////////33/////////////////////////////////////////////
				//strlen（str）-1得到的区间为[-1,18]
				//      ------聂敏慧
				//在工程中运行能够报出OOB，在这个测试框架中报出的是OK
				{
					"#include<string.h>"                                                   +"\n"+
							"#include <stdio.h>"                                                                     +"\n"+
							"int main()"                                                               +"\n"+
							"{"                                                                    +"\n"+
							"    char str[20] = \"he\";"                                             +"\n"+
							""                                                             +"\n"+
							"    if (str[strlen(str)-1] == 'e'){"                                  +"\n"+
							"        str[strlen(str)-1] = 'i';"                                    +"\n"+
							"    }"                                                                +"\n"+
							"    return 0 ;"                                                             +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////////////34/////////////////////////////////////////////
				{
					"#define MAX 10"                                                       +"\n"+
							"#define NONE 0xffffffff;"                                             +"\n"+
							""                                                                     +"\n"+
							"static int buf[MAX+1];"                                               +"\n"+
							"static unsigned int index = NONE;"                                    +"\n"+
							""                                                                     +"\n"+
							"void func()"                                                          +"\n"+
							"{"                                                                    +"\n"+
							"	if (index <= MAX)"                                                   +"\n"+
							"		buf[index] = 0; //FP"                                               +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////////////35/////////////////////////////////////////////
				{
					"#include <stdio.h>"                                                   +"\n"+
							""                                                                     +"\n"+
							"#define SIZE 10"                                                      +"\n"+
							""                                                                     +"\n"+
							"int *ptr = NULL;"                                                     +"\n"+
							"int buf[SIZE];"                                                       +"\n"+
							""                                                                     +"\n"+
							"void func1()"                                                         +"\n"+
							"{"                                                                    +"\n"+
							"	ptr = ptr + SIZE/38; //FP"                                            +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void func2()"                                                         +"\n"+
							"{"                                                                    +"\n"+
							"	ptr = buf;"                                                          +"\n"+
							"	func1();"                                                            +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////////////36/////////////////////////////////////////////
				{
					"#include <stdio.h>"                                                   +"\n"+
							""                                                                     +"\n"+
							"int *ptr = NULL;"                                                     +"\n"+
							"int buf[10];"                                                         +"\n"+
							""                                                                     +"\n"+
							"void func1()"                                                         +"\n"+
							"{"                                                                    +"\n"+
							"	ptr[5] = 0; //FP"                                                    +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void func2()"                                                         +"\n"+
							"{"                                                                    +"\n"+
							"	ptr = buf;"                                                          +"\n"+
							"	func1();"                                                            +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////////////37/////////////////////////////////////////////
				{
					"#define MAX 256"                                                      +"\n"+
							""                                                                     +"\n"+
							"void func2(unsigned int var)"                                         +"\n"+
							"{"                                                                    +"\n"+
							"	int buf[MAX];"                                                       +"\n"+
							""                                                                     +"\n"+
							"	buf[var] = 0;"                                                       +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void func()"                                                          +"\n"+
							"{"                                                                    +"\n"+
							"	unsigned int index;"                                                 +"\n"+
							""                                                                     +"\n"+
							"	index = (unsigned int)-1;"                                           +"\n"+
							""                                                                     +"\n"+
							"	if (index < MAX)"                                                    +"\n"+
							"		func2(index); //FP"                                                 +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////////////38/////////////////////////////////////////////
				//这个用例区间方面暂时还很难修改,目前修改不了
				//       ---------聂敏慧
				{
					"  void abv_iter1() {"                                                 +"\n"+
							"    int a[10];"                                                       +"\n"+
							"    int *p;"                                                          +"\n"+
							"    for (p = a; p < a+10; p++) {"                                     +"\n"+
							"      *p = 0;"                                                        +"\n"+
							"    }"                                                                +"\n"+
							"    p[1] = 11; //DEFECT"                                              +"\n"+
							"  }"                                                                  
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////////////39////////////////////////////////////////////
				{
					"int i;"                                                               +"\n"+
							"void f(){"                                                            +"\n"+
							"   i=10;"                                                             +"\n"+
							"}"                                                                    +"\n"+
							"void f1(){"                                                           +"\n"+
							"   int a[10];"                                                        +"\n"+
							"   i=1;"                                                              +"\n"+
							"   f();"                                                              +"\n"+
							"   a[i]=1;"                                                           +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},
				/////////////////////////40/////////////////////////////////////////////
				{
					"int* str=0;"                                                          +"\n"+
							"fun(int i){"                                                          +"\n"+
							"	int a[2];"                                                           +"\n"+
							"	if(i<10)"                                                            +"\n"+
							"		str[i]=a[0];"                                                       +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				
				/////////////////////////41/////////////////////////////////////////////
				{
					"#define  MAX 10"                                                      +"\n"+
							"int flag=MAX;"                                                        +"\n"+
							"f(){"                                                                 +"\n"+
							"    int a[MAX];"                                                      +"\n"+
							"	while(flag--)"                                                       +"\n"+
							"	{"                                                                   +"\n"+
							"		a[flag];"                                                           +"\n"+
							""                                                                     +"\n"+
							"	}"                                                                   +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////////////42/////////////////////////////////////////////
				{
					"f(){"                                                                 +"\n"+
							"   int a[10],j,i;"                                                        +"\n"+
							"   for(i=0;i<10;i++){"                                            +"\n"+
							"       a[i]=1;  "                                                     +"\n"+
							"   }"                                                                 +"\n"+
							"   "                                                                  +"\n"+
							"   if(i==10)  return;   "                                             +"\n"+
							"    j=a[i]; "                                                      +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////////////43/////////////////////////////////////////////
				{
					"void fFFF(){"                                                                 +"\n"+
							"   int a[10];"                                                        +"\n"+
							"   int i,j;"                                                            +"\n"+
							"   for(i=0;i<10;i++){"                                                +"\n"+
							"       a[i]=1;  "                                                     +"\n"+
							"   }"                                                                 +"\n"+
							"   "                                                                  +"\n"+
							"   j=a[i]; //DEFECT"                                                      +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},
				/////////////////////////44/////////////////////////////////////////////
				//区间错误，需要修改底层区间计算
				//         --------聂敏慧
				{
					"#include <stdlib.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"int a[100];"                                                          +"\n"+
							"void fun(){"                                                          +"\n"+
							"    int k=10,i;"                                                        +"\n"+
							"	for(i=0;i<20;i++)"                                               +"\n"+
							"		a[i*k]=0;"                                                          +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},
				/////////////////////////45/////////////////////////////////////////////
				//区间错误：j=atoi(current), j的区间[-inf,inf]，不方便修改
				//         --------聂敏慧
				//这个暂时修改不了
				{
					"#include <stdlib.h> "                                                 +"\n"+
							"#include <time.h>"                                                    +"\n"+
							""                                                                     +"\n"+
							"void f_OOB_1(char* current)"                                          +"\n"+
							"{"                                                                    +"\n"+
							"	int day[]={31,28,31,30,31,30,31,31,30,31,30,31};"                    +"\n"+
							"	int i=2011,j,k;"                                                     +"\n"+
							"	_strdate(current);"                                                  +"\n"+
							"	//..."                                                               +"\n"+
							"	j=atoi(current);//month"                                             +"\n"+
							"	k=atoi(current+3);//day"                                             +"\n"+
							"	if(k>1)"                                                             +"\n"+
							"	{"                                                                   +"\n"+
							"		//…"                                                                +"\n"+
							"	}"                                                                   +"\n"+
							"    else"                                                             +"\n"+
							"	{"                                                                   +"\n"+
							"		if(j==1){"                                                          +"\n"+
							"			i--;"                                                              +"\n"+
							"			j=12;"                                                             +"\n"+
							"		}"                                                                  +"\n"+
							"		j--;"                                                               +"\n"+
							"		if(j==2)"                                                           +"\n"+
							"		{"                                                                  +"\n"+
							"			if(j%4)k=28;"                                                      +"\n"+
							"			else if(j%100==0&&j%400)k=28;"                                     +"\n"+
							"			else k=29;"                                                        +"\n"+
							"		}"                                                                  +"\n"+
							"		else k=day[j-1];//OOB,day,false alarm"                              +"\n"+
							"	}"                                                                   +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},
				
				
				////////////////////////46/////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"#define BUFSIZE 10"                                                   +"\n"+
							""                                                                     +"\n"+
							"void zk_bo_19_f1()"                                                   +"\n"+
							"{"                                                                    +"\n"+
							"	int *buf;"                                                           +"\n"+
							""                                                                     +"\n"+
							"	buf = (int *)malloc(BUFSIZE * sizeof(int));"                         +"\n"+
							"	if (buf == NULL)"                                                    +"\n"+
							"		return;"                                                            +"\n"+
							"	buf[BUFSIZE+1] = 1; //DEFECT"                                        +"\n"+
							"	buf[-1] = 2; //DEFECT"                                               +"\n"+
							""                                                                     +"\n"+
							"	*(buf+BUFSIZE) = 12; //DEFECT"                                       +"\n"+
							"	*(buf-2) = 3; //DEFECT"                                              +"\n"+
							"	free(buf);"                                                          +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},
				
				/////////////////////////47/////////////////////////////////////////////
				{
					"#include <stdio.h>"                                                   +"\n"+
							""                                                                     +"\n"+
							"void zk_oob_4_f1(int *ptr)"                                           +"\n"+
							"{"                                                                    +"\n"+
							"	int i;"                                                              +"\n"+
							"	int buf[2];"                                                         +"\n"+
							""                                                                     +"\n"+
							"	for (i = 0; i < 3; i++) {"                                           +"\n"+
							"		if (ptr++ != NULL)"                                                 +"\n"+
							"			buf[i] = *ptr;"                                                    +"\n"+
							"	}"                                                                   +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},
				/////////////////////////48/////////////////////////////////////////////
				{
					"static int zk_oob_3_g1[10];"                                          +"\n"+
							""                                                                     +"\n"+
							"void zk_oob_3_f1(int val)"                                            +"\n"+
							"{"                                                                    +"\n"+
							"	int i = 1;"                                                          +"\n"+
							"    for(i=-1;i<10;i++)"                                               +"\n"+
							"	   zk_oob_3_g1[i]=val; //DEFECT"                                     +"\n"+
							"	for(i=0;i<11;i++)"                                                   +"\n"+
							"	   zk_oob_3_g1[i]=val; //DEFECT"                                     +"\n"+
							"		"                                                                   +"\n"+
							"	return;"                                                             +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},				
				/////////////////////////49/////////////////////////////////////////////
				{
					"#define MAX 5"                                                        +"\n"+
							""                                                                     +"\n"+
							"int g_val = 0;"                                                       +"\n"+
							""                                                                     +"\n"+
							"void func2(int);"                                                     +"\n"+
							""                                                                     +"\n"+
							"void func1(int var)"                                                  +"\n"+
							"{"                                                                    +"\n"+
							"	int array[MAX];"                                                     +"\n"+
							""                                                                     +"\n"+
							"	func2(var);"                                                         +"\n"+
							""                                                                     +"\n"+
							"	array[g_val] = g_val; //DEFECT"                                      +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void func2(int var)"                                                  +"\n"+
							"{"                                                                    +"\n"+
							"	if (var >= MAX) {"                                                   +"\n"+
							"		g_val = var + 1;"                                                   +"\n"+
							"	} else if (var < 0) {"                                               +"\n"+
							"		g_val = var;"                                                       +"\n"+
							"	} else {"                                                            +"\n"+
							"		g_val = -var;"                                                      +"\n"+
							"	}"                                                                   +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OOB"
							,
				},
				/////////////////////////50/////////////////////////////////////////////
				{
					"#define MAX 5"                                                        +"\n"+
							""                                                                     +"\n"+
							"int g_val = 0;"                                                       +"\n"+
							""                                                                     +"\n"+
							"void func2(int);"                                                     +"\n"+
							""                                                                     +"\n"+
							"void func1(int var)"                                                  +"\n"+
							"{"                                                                    +"\n"+
							"	int array[MAX], *ptr;"                                               +"\n"+
							""                                                                     +"\n"+
							"	ptr = array;"                                                    +"\n"+
							"	func2(var);"                                                         +"\n"+
							""                                                                     +"\n"+
							"	*(ptr + g_val) = g_val; //DEFECT"                                    +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void func2(int var)"                                                  +"\n"+
							"{"                                                                    +"\n"+
							"	if (var >= MAX) {"                                                   +"\n"+
							"		g_val = var + 1;"                                                   +"\n"+
							"	} else if (var < 0) {"                                               +"\n"+
							"		g_val = var;"                                                       +"\n"+
							"	} else {"                                                            +"\n"+
							"		g_val = -var;"                                                      +"\n"+
							"	}"                                                                   +"\n"+
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
