package softtest.test.c.gcc.test_team_1;

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
					///////////////// 0   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "#define BUFSIZE 10"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_bo_19_f1()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	int *buf;"                                                           +"\n"+
		            ""                                                                     +"\n"+
		            "	buf = (int *)malloc(10* sizeof(int));"                         +"\n"+
		            "	buf[BUFSIZE+1] = 1; //DEFECT"                                        +"\n"+
		            "	free(buf);"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB"
		            ,
		            },		            
		        	///////////////// 1   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "#define BUFSIZE 10"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_bo_19_f1()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	int *buf;"                                                           +"\n"+
		            ""                                                                     +"\n"+
		            "	buf = (int *)malloc(10* sizeof(int));"                         +"\n"+
		            "	buf[-1] = 2; //DEFECT"                                               +"\n"+
		            "	free(buf);"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB"
		            ,
		            },
		        	///////////////// 2   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "#define BUFSIZE 10"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_bo_19_f1()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	int *buf;"                                                           +"\n"+
		            ""                                                                     +"\n"+
		            "	buf = (int *)malloc(10* sizeof(int));"                         +"\n"+
		            "	*(buf+BUFSIZE) = 12; //DEFECT"                                       +"\n"+
		            "	free(buf);"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OOB"
		            ,
		            },
		        	///////////////// 3   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "#define BUFSIZE 10"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_bo_19_f1()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	int *buf;"                                                           +"\n"+
		            ""                                                                     +"\n"+
		            "	buf = (int *)malloc(10* sizeof(int));"                         +"\n"+
		            "	*(buf-2) = 3; //DEFECT"                                              +"\n"+
		            "	free(buf);"                                                          +"\n"+
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
