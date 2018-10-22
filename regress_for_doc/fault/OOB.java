package fault;

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
public class OOB {
	private String source = null;
	private String compiletype=null;
	private String result = null;
	private static final String fsmPath="softtest/rules/gcc/fault/OOB-0.1.xml";
	FSMAnalysisVisitor fsmAnalysis; 
	private FSMControlFlowData cfData;
	
	public OOB(String source,String compiletype, String result)
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
	/////////////////  0   ///////////////////	
		            {
		            "int c[5];"                                                            +"\n"+
		            "int test1 () {"                                                       +"\n"+
		            "	int a[] = {1,2,3,4,2};"                                              +"\n"+
		            "	a[6] = 1;  //DEFECT,OOB,a"                                           +"\n"+
		            "	a[5] = 1;	 //DEFECT,OOB,a"                                           +"\n"+
		            "	int b[5];"                                                           +"\n"+
		            "	b[6]; //DEFECT,OOB,b"                                                +"\n"+
		            "	c[6];  //DEFECT,OOB,c"                                               +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB"
		            ,
		            },

	/////////////////  2   ///////////////////	
		            {
		            "int c[3][3];"                                                         +"\n"+
		            "void f(){"                                                            +"\n"+
		            "	int b[3][3];"                                                        +"\n"+
		            "	b[1][1]=0;"                                                          +"\n"+
		            "	b[1][2]=0;"                                                          +"\n"+
		            "	b[3][1]=0;  //DEFECT,OOB,b"                                          +"\n"+
		            "	b[2][3]=0;  //DEFECT,OOB,b"                                          +"\n"+
		            "	b[2][2]=0;  //FP,OOB"                                                +"\n"+
		            "	c[1][3]=0;  //DEFECT,OOB,c"                                          +"\n"+
		            "	c[3][1]=0;  //DEFECT,OOB,c"                                          +"\n"+
		            "	char g[3]={\"ac\"};"                                                   +"\n"+
		            "	g[3] = 'c';  //DEFECT,OOB,g"                                         +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB"
		            ,
		            },

	/////////////////  3   ///////////////////	
		            {
		            "int i;"                                                               +"\n"+
		            "void f(){"                                                            +"\n"+
		            "	int b[][3]={{1,2,4},{1,2,3},{1,2,3}};"                               +"\n"+
		            "	b[1][1]=0;"                                                          +"\n"+
		            "	b[1][2]=0;"                                                          +"\n"+
		            "	b[3][1]=0; //DEFECT,OOB,b"                                           +"\n"+
		            "	b[2][3]=0; //DEFECT,OOB,b"                                           +"\n"+
		            "	b[2][2]=0;  //FP,OOB"                                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB"
		            ,
		            },
	/////////////////  4   ///////////////////	
		            {
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
	///////////////// 5   ///////////////////	
		            {
		            ""                                                                     
		            ,
		            "gcc"
		            ,
		            "OOB"
		            ,
		            },
		            
	/////////////////  6   ///////////////////	
		            {
		            "int test1 () {"                                                       +"\n"+
		            "	int i ;"                                                             +"\n"+
		            "	int a[4] = {1,2,3,4};"                                               +"\n"+
		            "	if(i > 2)"                                                           +"\n"+
		            "	{ "                                                                  +"\n"+
		            "		a[i] = 1; //DEFECT,OOB,a"                                           +"\n"+
		            "	}	"                                                                  +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB"
		            ,
		            },

	/////////////////  7   ///////////////////	
		            {
		            "int test3 () {"                                                       +"\n"+
		            "	int i ;"                                                             +"\n"+
		            "	int a[4] = {1,2,3,4};"                                               +"\n"+
		            "	if(i > 0 || i < 3)"                                                  +"\n"+
		            "	{"                                                                   +"\n"+
		            "		a[i] = 1; //DEFECT,OOB,a"                                           +"\n"+
		            "	}"                                                                   +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB"
		            ,
		            },
	/////////////////  8   ///////////////////	
		            {
		            "int func1(int a) {"                                                   +"\n"+
		            "	int array[4];"                                                       +"\n"+
		            "	if (a > 4 || a < 0) {"                                               +"\n"+
		            "		return 0;"                                                          +"\n"+
		            "	}"                                                                   +"\n"+
		            "	array[a] = 1;  //DEFECT,OOB,array"                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB"
		            ,
		            },
	/////////////////  9   ///////////////////	
		            {
		            "int func2(int a) {"                                                   +"\n"+
		            "	int array[4];"                                                       +"\n"+
		            "	if (a>=0 && a<=4) {"                                                 +"\n"+
		            "		array[a] = 1;  //DEFECT,OOB,array"                                  +"\n"+
		            "	}"                                                                   +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB"
		            ,
		            },
	/////////////////  10   ///////////////////	
		            {
		            "typedef struct _Test {"                                               +"\n"+
		            "	int a[2];"                                                           +"\n"+
		            "} Test;"                                                              +"\n"+
		            "int test1()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	Test st[2] = {0};"                                                   +"\n"+
		            "	st[0].a[0] = 1;"                                                     +"\n"+
		            "	st[0].a[1] = 1;"                                                     +"\n"+
		            "	st[2].a[0] = 1;  //DEFECT,OOB,st"                                    +"\n"+
		            "	st[2].a[2] = 1;  //DEFECT,OOB,st"                                    +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB"
		            ,
		            },
	/////////////////  11   ///////////////////	
		            {
		            "#define MAX 10"                                                       +"\n"+
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

	            
	            
		 });
	 }
}
