package softtest.test.keilc.rules.fault;

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
public class Test_OOBSUMMARY {
	private String source = null;
	private String compiletype=null;
	private String result = null;
	private static final String fsmPath="softtest/rules/keilc/fault/OOBSUMMARY-0.1.xml";
	FSMAnalysisVisitor fsmAnalysis; 
	private FSMControlFlowData cfData;
	
	public Test_OOBSUMMARY(String source,String compiletype, String result)
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
		            "	f1(5);"                                                              +"\n"+
		            "	f1(j); return 2;"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int f3(){"                                                            +"\n"+
		            "	int k=10;"                                                           +"\n"+
		            "	f2(k);//FP,OOBSUMMARY"                                                              +"\n"+
		            "	return 3;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "OOBSUMMARY"
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
		            "keil"
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
		            "keil"
		            ,
		            "OOBSUMMARY"
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
		            "keil"
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
		            "keil"
		            ,
		            "OOBSUMMARY"
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
		            "keil"
		            ,
		            "OOBSUMMARY"
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
		            "keil"
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
		            "keil"
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
		            "keil"
		            ,
		            "OOBSUMMARY"
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
		            "keil"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  10   ///////////////////	
		            {//zys:不生成函数摘要，由普通的OOB进行检测，所以会形成误报
		            "int k;"                                                               +"\n"+
		            "f1(int i){"                                                           +"\n"+
		            "char buf[10];"                                                        +"\n"+
		            "i=k;buf[i]=1;"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "f2(){"                                                                +"\n"+
		            "k=9;"                                                                +"\n"+
		            "f1(k);"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "OOBSUMMARY"
		            ,
		            },
	/////////////////  11   ///////////////////	
		            {
		            "int k=10;"                                                            +"\n"+
		            "f1(int i){"                                                           +"\n"+
		            "char buf[10];"                                                        +"\n"+
		            "buf[i]=1;"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "f2(){"                                                                +"\n"+
		            "f1(k);"                                                               +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "OOBSUMMARY"
		            ,
		            },
		        	/////////////////  12   ///////////////////	
		            {
		            "int k;"                                                            +"\n"+
		            "f1(int i){"                                                           +"\n"+
		            "char buf[10];"                                                        +"\n"+
		            "buf[i]=1;"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "f2(){"                                                                +"\n"+
		            "f1(k);"                                                               +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  13   ///////////////////	
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
		            "keil"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  14   ///////////////////	
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
		            "keil"
		            ,
		            "OOBSUMMARY"
		            ,
		            },
		        	/////////////////  15   ///////////////////	
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
		            "keil"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  16   ///////////////////	
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
		            "keil"
		            ,
		            "OK"
		            ,
		            },		            
	/////////////////  17   ///////////////////	
		            {//zys:错误原因：C中不允许同名函数（多态）
		            "void jhb_oob_2_fl(int x)"                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "	int local_array[7];"                                                 +"\n"+
		            "	local_array[x]=0;"                                                   +"\n"+
		            "}"                                                                    +"\n"+
		            "int jhb_oob_2_f(){"                                                  +"\n"+
		            "	jhb_oob_2_fl(15);   //DEFECT"                                        +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "OOBSUMMARY"
		            ,
		            },
	/////////////////  18   ///////////////////	
		            {//漏报原因：a[k*i]的下标关联变量无法确定。。。
		            "int a[100];"                                                          +"\n"+
		            "void fun(int i){"                                                     +"\n"+
		            "   int k=10;"                                                         +"\n"+
		            "	a[k*i]=1;//*(a+i+j)=a[i+j]"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            "f(){"                                                                 +"\n"+
		            "	fun(10);//DEFECT"                                                    +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OOBSUMMARY"
		            ,
		            },
		        	/////////////////  19   ///////////////////	
		            //区间有问题
		            {
		            "int k;"                                                               +"\n"+
		            "f1(int i){"                                                           +"\n"+
		            "char buf[10];"                                                        +"\n"+
		            "buf[i]=1;k=10;"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "f2(){"                                                                +"\n"+
		            "k=9;"                                                                +"\n"+
		            "f1(k);"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "OK"
		            ,
		            },    
		        	/////////////////  20：利用函数后置条件，不在本模式中检测，而在OOB中检测   ///////////////////	
		            {
		            "int k;"                                                               +"\n"+
		            "f1(){"                                                           +"\n"+
		            "k++;"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "f2(){"                                                                +"\n"+
		            "int a[10];k=9;"                                                                +"\n"+
		            "f1();a[k]=5;"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "keil"
		            ,
		            "OK"
		            ,
		            }, 
		          	/////////////////  21   ///////////////////	
		            {
		            "int k;"                                                               +"\n"+
		            "f1(int i){"                                                           +"\n"+
		            "char buf[10];"                                                        +"\n"+
		            "buf[i]=1;k=10;"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "f2(){"                                                                +"\n"+
		            "k=9;"                                                                +"\n"+
		            "f1(k);k++;"                                                                +"\n"+
		            "}f3(){f2();}"                                                                    
		            ,
		            "keil"
		            ,
		            "OK"
		            ,
		            }, 
		        	/////////////////  22   ///////////////////	
		            {
		            "int k=10;"                                                               +"\n"+
		            "f1(int i){"                                                           +"\n"+
		            "char buf[10];"                                                        +"\n"+
		            "buf[i]=1;k++;"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "f2(){"                                                                +"\n"+
		            "k=9;"                                                                +"\n"+
		            "f1(k);k++;"                                                                +"\n"+
		            "}f3(){f2();}"                                                                    
		            ,
		            "keil"
		            ,
		            "OK"
		            ,
		            }, 
		        	/////////////////  23   ///////////////////	
		            {
		            "int k;"                                                               +"\n"+
		            "f1(int i){"                                                           +"\n"+
		            "char buf[10];"                                                        +"\n"+
		            "buf[i]=1;k++;"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "f2(){"                                                                +"\n"+
		            "k=9;"                                                                +"\n"+
		            "f1(k);k++;"                                                                +"\n"+
		            "}f3(){f2();}"                                                                    
		            ,
		            "keil"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  24   ///////////////////
		            //全局在某节点的值为null,取了初始值？？？
		            {
		            "int k=10;"                                                               +"\n"+
		            "f1(int i){"                                                           +"\n"+
		            "char buf[10];"                                                        +"\n"+
		            "buf[i]=1;k++;"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "f2(){"                                                                +"\n"+
		            "f1(k);"                                                                +"\n"+
		            "k++;"                                                                +"\n"+
		            "}f3(){f2();}"                                                                    
		            ,
		            "keil"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  25   ///////////////////	
		            {
		            "int k=10;"                                                               +"\n"+
		            "f1(int i){"                                                           +"\n"+
		            "char buf[10];"                                                        +"\n"+
		            "buf[i]=1;k++;"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "f2(){"                                                                +"\n"+
		            "k--;f1(k);"                                                                +"\n"+
		            "k++;"                                                                +"\n"+
		            "}f3(){f2();}"                                                                    
		            ,
		            "keil"
		            ,
		            "OK"
		            ,
		            },
		            
		            
		 });
	 }
}
