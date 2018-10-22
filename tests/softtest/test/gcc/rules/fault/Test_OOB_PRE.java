package softtest.test.gcc.rules.fault;

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
public class Test_OOB_PRE {
	private String source = null;
	private String compiletype=null;
	private String result = null;
	private static final String fsmPath="softtest/rules/gcc/fault/OOB_PRE-0.1.xml";
	FSMAnalysisVisitor fsmAnalysis; 
	private FSMControlFlowData cfData;
	
	public Test_OOB_PRE(String source,String compiletype, String result)
	{
		this.source=source;	
		this.compiletype=compiletype;
		this.result = result;
	}

	@BeforeClass
	public static void setUpBase()
	{
//		BasicConfigurator.configure();
//        PropertyConfigurator.configure("log4j.properties") ;
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
		astroot.jjtAccept(new DUAnalysisVisitor(), null);
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
		            "int f1(int i){"                                                       +"\n"+
		            "	char buf[10];"                                                       +"\n"+
		            "	buf[i]=5;"                                                           +"\n"+
		            "	return 1;"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int f2(int j){"                                                       +"\n"+
		            "	f1(5);f1(j);"                                                              +"\n"+
		            "	return 2;"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int f3(){"                                                            +"\n"+
		            "	int k=10;"                                                           +"\n"+
		            "	f2(k);//FP,OOB_PRE"                                                              +"\n"+
		            "	return 3;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB_PRE"
		            ,
		            },
/////////////////  1   ///////////////////	
		            {
		            "int f1(int i){"                                                       +"\n"+
		            "	char buf[10];"                                                       +"\n"+
		            "	buf[i]=5;"                                                           +"\n"+
		            "	return 1;"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int f2(int j){"                                                       +"\n"+
		            "	f1(j);"                                                              +"\n"+
		            "	return 2;"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int f3(){"                                                            +"\n"+
		            "	int k=9;"                                                           +"\n"+
		            "	f2(k);"                                                              +"\n"+
		            "	return 3;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },		
/////////////////  2   ///////////////////	
		            {
		            "int f1(int i){"                                                       +"\n"+
		            "	char buf[10];"                                                       +"\n"+
		            "	buf[i]=5;"                                                           +"\n"+
		            "	return 1;"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int f2(int j){"                                                       +"\n"+
		            "	j=10;"                                                              +"\n"+
		            "	f1(j);//FP"                                                              +"\n"+
		            "	return 2;"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int f3(){"                                                            +"\n"+
		            "	int k=9;"                                                           +"\n"+
		            "	f2(k);"                                                              +"\n"+
		            "	return 3;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB_PRE"
		            ,
		            },		            
/////////////////  3   ///////////////////	
		            {
		            "int f1(int i){"                                                       +"\n"+
		            "	char buf[10];"                                                       +"\n"+
		            "	buf[i]=5;"                                                           +"\n"+
		            "	return 1;"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int f2(int j){"                                                       +"\n"+
		            "	j=9;"                                                              +"\n"+
		            "	f1(j);//FP"                                                              +"\n"+
		            "	return 2;"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int f3(){"                                                            +"\n"+
		            "	int k=10;"                                                           +"\n"+
		            "	f2(k);"                                                              +"\n"+
		            "	return 3;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },			            
/////////////////  4   ///////////////////	
		            {
		            "f1(int i){"                                                           +"\n"+
		            "char buf[10];"                                                        +"\n"+
		            "buf[i]=1;"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "f2(){"                                                                +"\n"+
		            "f1(10);"                                                              +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB_PRE"
		            ,
		            },
/////////////////  5   ///////////////////	
		            {
		            "f1(int i){"                                                           +"\n"+
		            "char buf[10];"                                                        +"\n"+
		            "buf[i]=1;"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "f2(){"                                                                +"\n"+
		            "int a=4,b=6;"                                                         +"\n"+
		            "f1(a+b);"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB_PRE"
		            ,
		            },
/////////////////  6   ///////////////////	
		            {
		            "f1(int i){"                                                           +"\n"+
		            "char buf[10];"                                                        +"\n"+
		            "buf[i]=1;"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "f2(){"                                                                +"\n"+
		            "int a=3,b=6;"                                                         +"\n"+
		            "f1(a+b);"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },		            
/////////////////  7   ///////////////////	
		            {
		            "f1(int i){"                                                           +"\n"+
		            "char buf[10];"                                                        +"\n"+
		            "buf[i]=1;"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "f2(){"                                                                +"\n"+
		            "int a,b=6;"                                                         +"\n"+
		            "f1(a+b);"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },		            
/////////////////  8   ///////////////////	
		            {
		            "int k;"                                                               +"\n"+
		            "f1(int i){"                                                           +"\n"+
		            "char buf[10];"                                                        +"\n"+
		            "buf[i]=1;"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "f2(){"                                                                +"\n"+
		            "k=10;"                                                                +"\n"+
		            "f1(k);"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB_PRE"
		            ,
		            },
/////////////////  9   ///////////////////	
		            {
		            "int k;"                                                               +"\n"+
		            "f1(int i){"                                                           +"\n"+
		            "char buf[10];"                                                        +"\n"+
		            "buf[i]=1;"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "f2(){"                                                                +"\n"+
		            "k=9;"                                                                +"\n"+
		            "f1(k);"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },

/////////////////  10  zys 2011.6.25	全局变量不再取其初始值///////////////////	
		            {
		            "int k=10;"                                                            +"\n"+
		            "f1(int i){"                                                           +"\n"+
		            "char buf[10];"                                                        +"\n"+
		            "buf[i]=1;"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "f2(){int b=k;"                                                                +"\n"+
		            "f1(b);"                                                               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
/////////////////  11   ///////////////////	
		            {
		            "f1(int i,int j){"                                                     +"\n"+
		            "char buf[10][5];"                                                     +"\n"+
		            "buf[i][j]=1;"                                                         +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "f2(){"                                                                +"\n"+
		            "f1(9,4);"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
/////////////////  12   ///////////////////	
		            {
		            "f1(int i,int j){"                                                     +"\n"+
		            "char buf[10][5];"                                                     +"\n"+
		            "buf[i][j]=1;"                                                         +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "f2(){"                                                                +"\n"+
		            "f1(10,4);"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB_PRE"
		            ,
		            },
/////////////////  13   ///////////////////	
		            {
		            "f1(int i,int j){"                                                     +"\n"+
		            "char buf[10][5];"                                                     +"\n"+
		            "buf[i][1]=1;"                                                         +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "f2(){"                                                                +"\n"+
		            "f1(1,20);"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  14   ///////////////////	
		            {
		            "f1(int i,int j){"                                                     +"\n"+
		            "char buf[10][5];"                                                     +"\n"+
		            "buf[1][1]=1;"                                                         +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "f2(){"                                                                +"\n"+
		            "f1(20,20);"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },		        

	/////////////////  15  ///////////////////	
		            {
		            "int k=10;"                                                            +"\n"+
		            "f0(){"                                                           +"\n"+
		            ""                                                        +"\n"+
		            "k=3;"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            "f1(){"                                                           +"\n"+
		            "char buf[10];"                                                        +"\n"+
		            "buf[k]=1;"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "f2(){"                                                                +"\n"+
		            "f0();"                                                               +"\n"+
		            "f1();"                                                               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },   
////////////////	/  16 ///////////////////	
		            {
		            ""                                                       +"\n"+
		            "void f(int i){"                                                       +"\n"+
		            "   int a[10];"                                                        +"\n"+
		            "   a[i]=1; //defect"                                                          +"\n"+
		            "     if(i>10)"                                                            +"\n"+
		            "   i++;"                                                  +"\n"+
		            "}"                                                             +"\n"+                                                              
		            "void f1(){"                                                      +"\n"+
		            "     int i=10;"                                                           +"\n"+
		            "     f(i);}" 
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  17   ///////////////////	
		            {
		            "void f(int i){"                                                       +"\n"+
		            "     int a[10];"                                                      +"\n"+
		            "     a[i]=1;"                                                         +"\n"+
		            "}"                                                                    +"\n"+
		            "void f1(int i){"                                                      +"\n"+
		            "     f(i);"                                                           +"\n"+
		            "     if(i>10)"                                                        +"\n"+
		            "     i++;"                                                            +"\n"+
		            "} "                                                                   +"\n"+
		            "void f2(){"                                                           +"\n"+
		            "int a=10;"                                                            +"\n"+
		            "f1(a);"                                                               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },	            
		 });
	 }
}

