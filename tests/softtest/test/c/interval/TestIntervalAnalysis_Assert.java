package softtest.test.c.interval;

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

import java.util.Hashtable;
import java.util.List;


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
import softtest.ast.c.Node;
import softtest.ast.c.ParseException;

import softtest.cfg.c.ControlFlowVisitor;
import softtest.cfg.c.Graph;
import softtest.cfg.c.VexNode;
import softtest.config.c.Config;
import softtest.domain.c.analysis.ControlFlowDomainVisitor;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.symbolic.Expression;
import softtest.domain.c.symbolic.SymbolFactor;

import softtest.fsmanalysis.c.CAnalysis;
import softtest.fsmanalysis.c.UnknownString;

import softtest.fsmanalysis.c.FSMControlFlowData;

import softtest.pretreatment.PlatformType;
import softtest.pretreatment.Pretreatment;

import softtest.symboltable.c.OccurrenceAndExpressionTypeFinder;
import softtest.symboltable.c.ScopeAndDeclarationFinder;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.tools.c.jaxen.MatchesFunction;
@RunWith(Parameterized.class)
public class TestIntervalAnalysis_Assert
{
	private String source = null;
	private String vexstr = null;
	private String varstr =null;
	private String valuestr=null;
	private String domainstr=null;
	


	static Pretreatment pre = new Pretreatment();

	static int testcaseNum = 0;

	String temp;// 预处理后的中间文件

	public TestIntervalAnalysis_Assert(String source, String vexstr, String varstr, String valuestr, String domainstr) {
		this.source = source;
		this.vexstr = vexstr;
		this.varstr = varstr;
		this.valuestr = valuestr;
		this.domainstr = domainstr;
	}

	@BeforeClass
	public static void setUpBase()
	{
		
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
		MatchesFunction.registerSelfInSimpleContext();
		Config.REGRESS_RULE_TEST=true;
	}

	// 根据不同的模式需求，自行分配当前AST分析到的步骤
	private void analysis(ASTTranslationUnit astroot)
	{
		astroot.jjtAccept(new ScopeAndDeclarationFinder(), null);
		astroot.jjtAccept(new OccurrenceAndExpressionTypeFinder(), null);
		astroot.jjtAccept(new ControlFlowVisitor(), null);
		SymbolFactor.resetNameCount();
		astroot.jjtAccept(new ControlFlowDomainVisitor(), null);
		
		String value="ERROR",domain="ERROR";
		List<Node> mds = astroot.findChildrenOfType(ASTFunctionDefinition.class);
		if (!mds.isEmpty()) {
			Graph g = ((ASTFunctionDefinition)mds.get(0)).getGraph();
			VexNode vn = g.nodes.get(vexstr);
			Hashtable<VariableNameDeclaration, Expression> vTable=vn.getValueSet().getTable();
			for (VariableNameDeclaration vv : vTable.keySet()) {
				if (vv.getImage().equals(varstr)) {
					Expression e = vTable.get(vv);
					if (e != null) {
						value = e.toString();
						Domain dm=vn.getDomain(vv);
						if(dm!=null){
							domain=dm.toString();
						}
					}
					break;
				}
			}
		}
		
//		assertEquals("interval analyssi error",valuestr,value);
		assertEquals("interval analyssi error",domainstr,domain);
	}


	@Before
	public void init()
	{


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
		UnknownString.setReplaceString();
		temp = CAnalysis.fileReplace(temp);
		
	}

	@After
	public void shutdown()
	{
		
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
			/*暂时屏蔽KEIL下的区间处理			
			CParser.setType("keil");
			try {
				keil_astroot= parser_keil.TranslationUnit();
			} catch (ParseException e) {
				e.printStackTrace();
				fail("parse error");
			}
			analysis(keil_astroot);
			*/	
			
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
	            "#include<assert.h>"                                                       +"\n"+
	            "void f(int i){"                                                       +"\n"+
	            "	assert(i==10);"                                                                +"\n"+
	            "	int j=i/10;"                                                                +"\n"+                                                         
	            "}"                                                                    
	            ,
	            "decl_stmt_2"
	            ,
	            "j"
	            ,
	            "1"
	            ,
	            "[1,1]"
	            ,
	            },
/////////////////  01   ///////////////////	
	            {
	            "#include<assert.h>"                                                       +"\n"+
	            "void f(int i){"                                                       +"\n"+
	            "	assert(i!=0);"                                                                +"\n"+
	            "	int j=i/10;"                                                                +"\n"+                                                         
	            "}"                                                                    
	            ,
	            "decl_stmt_2"
	            ,
	            "j"
	            ,
	            "0.1*i_01"
	            ,
	            "[-inf,-1]U[0,inf]"
	            ,
	            },
/////////////////  02   ///////////////////	
	            {
	            "#include<stdlib.h> "                                                       +"\n"+
	            "void f(int i){"                                                       +"\n"+
	            "	VOS_Assert_X(i!=0);"                                                                +"\n"+
	            "	int j=i/10;"                                                                +"\n"+                                                         
	            "}"                                                                    
	            ,
	            "decl_stmt_4"
	            ,
	            "j"
	            ,
	            "0.1*i_01"
	            ,
	            "[-inf,-1]U[0,inf]"
	            ,
	            },
/////////////////  03   ///////////////////	
	            {
	            "#include<stdlib.h> "                                                       +"\n"+
	            "void f(int k){"                                                       +"\n"+
	            "	VOS_Assert_X((k<100)&&(k>90));"                                                                +"\n"+
	            "	int j=k/10;"                                                                +"\n"+                                                         
	            "}"                                                                    
	            ,
	            "decl_stmt_4"
	            ,
	            "j"
	            ,
	            "0.1*k_01"
	            ,
	            "[9,9]"
	            ,
	            },
		});
	}
}
