package softtest.test.c.rules;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

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
import softtest.fsmanalysis.c.CAnalysis;
import softtest.fsmanalysis.c.FSMAnalysisVisitor;
import softtest.fsmanalysis.c.FSMControlFlowData;
import softtest.fsmanalysis.c.Report;
import softtest.fsmanalysis.c.UnknownString;
import softtest.interpro.c.InterCallGraph;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.InterMethodVisitor;
import softtest.pretreatment.PlatformType;
import softtest.pretreatment.Pretreatment;
import softtest.summary.lib.c.LibManager;
import softtest.symboltable.c.AbstractScope;
import softtest.symboltable.c.OccurrenceAndExpressionTypeFinder;
import softtest.symboltable.c.ScopeAndDeclarationFinder;

/**
 * 模式测试时所有测试类的基类，提供了预编译、自动机分析等功能
 * @author zys	
 * 2010-3-10
 * 
 * 修改各模式的回归测试框架
 * 2010.8.13
 */
public class ModelTestBase{
	//源代码，编译类型，预期结果
	String source = null;
	String compiletype=null;
	String result = null;
	
	//待回归的自动机XML描述文件路径
	protected static String fsmPath;
	
	//库函数摘要路径
	protected static String LIB_SUMMARYS_PATH;
	
	FSMAnalysisVisitor fsmAnalysis; 
	FSMControlFlowData cfData;
	
	protected static Pretreatment pre=new Pretreatment();
	protected static LibManager libManager = LibManager.getInstance();
	protected static InterContext interContext = InterContext.getInstance();
	
	//预处理后的中间文件及其编号
	static int testcaseNum=0;
	String temp;
	
	public ModelTestBase(String source,String compiletype, String result)
	{
		this.source=source;	
		this.compiletype=compiletype;
		this.result = result;
	}

	/**1、每次回归仅执行一次，相当于全局的初始化功能；
	 * 2、执行次序优先于子类的@BeforeClass函数 */
	@BeforeClass
	public static void setUpBase()
	{
		CAnalysis.deleteAndCreateTemp(Config.PRETREAT_DIR);
		
		pre.setPlatform(PlatformType.GCC);
		
		List<String> include = new ArrayList<String>();
		
		String INCLUDE = System.getenv("GCCINC");
		if(INCLUDE==null){
			throw new RuntimeException("System environment variable \"GCCINC\" error!");
		}
		String[] Inctemp = INCLUDE.split(";");
		if(Config.GCC_TYPE==0){
			for(int i = 0;i<Inctemp.length;i++){
				Pretreatment.systemInc.add(Inctemp[i]);
				include.add(Inctemp[i]);
			}
		}else if(Config.GCC_TYPE==1){
			for(int i = 0;i<Inctemp.length;i++){
				Inctemp[i]=Inctemp[i].replace('\\', '/');
				Pretreatment.systemInc.add(Inctemp[i]);
				include.add(Inctemp[i]);
			}
			Pretreatment.systemInc.add("/usr/include");
			Pretreatment.systemInc.add("/usr/local/include");
		}
		pre.setInclude(include);
		// chh 初始化不能识别而需要替换的字符串序列 
		UnknownString.setReplaceString();
		Config.REGRESS_RULE_TEST=true;
	}
	
	/**1、每次回归仅执行一次，相当于全局的后期处理操作（清空操作）
	 * 2、执行次序？ */
	@AfterClass
	public static void clear()
	{
		//interContext.getLibMethodDecls().clear();
		InterContext.clear();
	}
	
	/**1、每个测试用例执行时，首先执行本用例的初始化工作 */
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
		
		temp=pre.pretreat(tempFile.getAbsolutePath(), pre.getInclude(), new ArrayList<String>());
		//chh  替换不能识别的字符串
		if(Config.FILEREPLACE)
			temp=CAnalysis.fileReplace(temp);
	}

	/**1、回归测试核心代码 */
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
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}
	}
	
	/**根据不同的模式需求，自行分配当前AST分析到的步骤 */
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
		astroot.jjtAccept(new DUAnalysisVisitor(), null);
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
}
