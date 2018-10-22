package softtest.test.c.callgraph;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import org.jaxen.JaxenException;
import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.CCharStream;
import softtest.ast.c.CParser;
import softtest.ast.c.ParseException;
import softtest.ast.c.SimpleNode;
import softtest.callgraph.c.CGraph;
import softtest.callgraph.c.CVexNode;
import softtest.cfg.c.ControlFlowVisitor;
import softtest.cfg.c.Graph;
import softtest.config.c.Config;
import softtest.fsmanalysis.c.CAnalysis;
import softtest.pretreatment.PlatformType;
import softtest.pretreatment.Pretreatment;
import softtest.summary.lib.c.LibManager;
import softtest.symboltable.c.AbstractScope;
import softtest.symboltable.c.OccurrenceAndExpressionTypeFinder;
import softtest.symboltable.c.ScopeAndDeclarationFinder;
import softtest.symboltable.c.Type.CType;
import softtest.tools.c.jaxen.MatchesFunction;

/**
 * @author Liuli
 *2010-4-9
 */
@RunWith(Parameterized.class)
public class TestCallGraphVisitor
{
	private String source = null;
	private String compiletype=null;
	private String graphStr = null;
	static int testcaseNum=0;
	static Pretreatment pre=new Pretreatment();
	static String temp;
	static LibManager libManager = LibManager.getInstance();
	
	public TestCallGraphVisitor(String source,String compiletype, String graphStr) {
		this.source = source;
		this.compiletype=compiletype;
		this.graphStr = graphStr;
	}
	
	@BeforeClass
	public static void setUpBase()  {
		CAnalysis.deleteAndCreateTemp(Config.PRETREAT_DIR);
	}

	@AfterClass
	public static void tearDownBase() {
	}
	
	private void analysis(ASTTranslationUnit astroot){
		astroot.jjtAccept(new ScopeAndDeclarationFinder(), null);
		astroot.jjtAccept(new OccurrenceAndExpressionTypeFinder(), null);
		astroot.jjtAccept(new ControlFlowVisitor(), null);
		
		CGraph g = new CGraph();
		((AbstractScope)(astroot.getScope())).resolveCallRelation(g);
		List<CVexNode> list = g.getTopologicalOrderList();
		Collections.reverse(list);
		
		String graphString="";
		try {
				if(g!=null){
					graphString=g.toString();
				}
			} catch (Exception e) {
				e.printStackTrace();
			} 		
			assertEquals(""+CParser.getType()+" type error",graphStr,graphString);	
	}

	@Before
	public void init() {
		String tempName="CG_"+ (testcaseNum++) +".c";
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
		
		String INCLUDE = null;
		if(compiletype.equals("gcc")){
			pre.setPlatform(PlatformType.GCC);
			INCLUDE = System.getenv("GCCINC");
			if(INCLUDE==null){
				throw new RuntimeException("System environment variable \"GCCINC\" error!");
			}
		}else if(compiletype.equals("keil")){
			pre.setPlatform(PlatformType.KEIL);
			INCLUDE = System.getenv("GCCINC");
			if(INCLUDE==null){
				throw new RuntimeException("System environment variable \"GCCINC\" error!");
			}
		}
		String[] Inctemp = INCLUDE.split(";");
		for(int i = 0;i<Inctemp.length;i++){
			Pretreatment.systemInc.add(Inctemp[i]);
		}
		String headers[]=Config.LIB_HEADER_PATH.split(";");
		for(int i=0;i<headers.length;i++){
			Pretreatment.systemInc.add(headers[i]);
		}
		temp=pre.pretreat(tempFile.getAbsolutePath(), new ArrayList<String>(), new ArrayList<String>());
	}

	@After
	public void shutdown() {
		//清除临时文件夹
	}
	
	@Test
	public void test() {
		try {
			CParser.setType("gcc");
			CParser parser_gcc = CParser.getParser(new CCharStream(
					new FileInputStream(temp)));
			CParser.setType("keil");
			CParser parser_keil = CParser.getParser(new CCharStream(
					new FileInputStream(temp)));
			ASTTranslationUnit gcc_astroot = null, keil_astroot = null;
			if (compiletype.equals("gcc")) {
				CParser.setType("gcc");
				try {
					gcc_astroot = parser_gcc.TranslationUnit();
				} catch (ParseException e) {
					e.printStackTrace();
					fail("parse error");
				}
				analysis(gcc_astroot);
			} else if (compiletype.equals("keil")) {
				CParser.setType("keil");
				try {
					keil_astroot = parser_keil.TranslationUnit();
				} catch (ParseException e) {
					e.printStackTrace();
					fail("parse error");
				}
				analysis(keil_astroot);
			} else {
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
					keil_astroot = parser_keil.TranslationUnit();
				} catch (ParseException e) {
					e.printStackTrace();
					fail("parse error");
				}
				analysis(keil_astroot);
			}
		} catch (FileNotFoundException e1) {
			e1.printStackTrace();
		}
	}
	
	@Parameters
	public static Collection<Object[]> testcaseAndResults(){
		return Arrays.asList(new Object[][] {
/////////////////  0   ///////////////////	
	            {
	            "int count=0;"                                                         +"\n"+
	            ""                                                                     +"\n"+
	            "void f1(int i)"                                                       +"\n"+
	            "{"                                                                    +"\n"+
	            "	f2();"                                                               +"\n"+
	            "	f3(30);"                                                             +"\n"+
	            "	if(count++<10)"                                                      +"\n"+
	            "		f1(5);"                                                             +"\n"+
	            "}"                                                                 +"\n"+
	            "int f2()"                                                             +"\n"+
	            "{"                                                                    +"\n"+
	            "	f3(30);"                                                             +"\n"+
	            "}"                                                                    +"\n"+
	            "int f3(int c)"                                                        +"\n"+
	            "{"                                                                    +"\n"+
	            "	printf(\"hello from f2()!	count=%d\\n\",count);"                        +"\n"+
	            "	return 33;"                                                          +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "int main()"                                                           +"\n"+
	            "{"                                                                    +"\n"+
	            "	f1(1);"                                                              +"\n"+
	            "	return 0;"                                                           +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "Graph {"                                                        +"\n"+
                "  main_0_1"                                        +"\n"+
                "  f2_0_3"                                        +"\n"+
                "  f3_1_2"                                        +"\n"+
                "  f1_1_0"                                        +"\n"+
                "  f1_1_0 -> f2_0_3"                                        +"\n"+
                "  f2_0_3 -> f3_1_2"                                        +"\n"+
                "  f1_1_0 -> f3_1_2"                                        +"\n"+
                "  main_0_1 -> f1_1_0"                                        +"\n"+
                "  f1_1_0 -> f1_1_0"                                        +"\n"+                                               
                "}"
	            ,
	            },
//////	      1   ///////////////////	
	            {
	            "#include <stdio.h>"                                                   +"\n"+
	            "int i=0;"                                                             +"\n"+
	            "void a();"                                                            +"\n"+
	            "void c(){"                                                            +"\n"+
	            "	"                                                                    +"\n"+
	            "	printf(\"c!\\n\");"                                                     +"\n"+
	            "	while(i++<5)"                                                        +"\n"+
	            "		a();"                                                               +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "void b(){"                                                            +"\n"+
	            "	printf(\"b!\\n\");"                                                     +"\n"+
	            "	c();"                                                                +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "void a(){"                                                            +"\n"+
	            "	printf(\"a!\\n\");"                                                     +"\n"+
	            "	if(i<5)"                                                             +"\n"+
	            "		b();"                                                               +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "int main(){"                                                          +"\n"+
	            "	a();"                                                                +"\n"+
	            "	printf(\"hello world!\\n\");"                                           +"\n"+
	            "	return 0;"                                                           +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "Graph {"                                                        +"\n"+
	                "  c_0_2"                                        +"\n"+
	                "  a_0_1"                                        +"\n"+
	                "  main_0_3"                                        +"\n"+
	                "  b_0_0"                                        +"\n"+
	                "  main_0_3 -> a_0_1"                                        +"\n"+
	                "  c_0_2 -> a_0_1"                                        +"\n"+
	                "  b_0_0 -> c_0_2"                                        +"\n"+
	                "  a_0_1 -> b_0_0"                                        +"\n"+
	            "}"
	            ,
	            },
/////////////////  2   ///////////////////	
	            {
	            "#include <stdio.h>"                                                   +"\n"+
	            "int i=0;"                                                             +"\n"+
	            ""                                                                     +"\n"+
	            "void c(){"                                                            +"\n"+
	            "	void a();"                                                           +"\n"+
	            "	printf(\"c!\\n\");"                                                     +"\n"+
	            "	while(i++<5)"                                                        +"\n"+
	            "		a();"                                                               +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "void b(){"                                                            +"\n"+
	            "	printf(\"b!\\n\");"                                                     +"\n"+
	            "	c();"                                                                +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "void a(){"                                                            +"\n"+
	            "	printf(\"a!\\n\");"                                                     +"\n"+
	            "	if(i<5)"                                                             +"\n"+
	            "		b();"                                                               +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "int main(){"                                                          +"\n"+
	            "	a();"                                                                +"\n"+
	            "	printf(\"hello world!\\n\");"                                           +"\n"+
	            "	return 0;"                                                           +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "Graph {"                                                        +"\n"+
	                "  c_0_2"                                        +"\n"+
	                "  a_0_1"                                        +"\n"+
	                "  main_0_3"                                        +"\n"+
	                "  b_0_0"                                        +"\n"+
	                "  main_0_3 -> a_0_1"                                        +"\n"+
	                "  c_0_2 -> a_0_1"                                        +"\n"+
	                "  b_0_0 -> c_0_2"                                        +"\n"+
	                "  a_0_1 -> b_0_0"                                        +"\n"+
	            "}"
	            ,
	            },				
/////////////////  3   ///////////////////	
	            {
	            "extern f();"                                                          +"\n"+
	            "void g(){"                                                            +"\n"+
	            "f();"                                                                 +"\n"+
	            "}"                                                                    +"\n"+
	            "int main(){"                                                          +"\n"+
	            "g();"                                                                 +"\n"+
	            "f();"                                                                 +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "Graph {"                                                        +"\n"+
	                "  main_0_1"                                        +"\n"+
	                "  g_0_0"                                        +"\n"+
	                "  main_0_1 -> g_0_0"                                        +"\n"+
	            "}"
	            ,
	            },
/////////////////  4   ///////////////////	
	            {
	            "#include <stdio.h>"                                                   +"\n"+
	            "int i=0;"                                                             +"\n"+
	            ""                                                                     +"\n"+
	            "void c(){	"                                                           +"\n"+
	            "	printf(\"c!\\n\");"                                                     +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "void b(){"                                                            +"\n"+
	            "	printf(\"b!\\n\");"                                                     +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "void a(){"                                                            +"\n"+
	            "	printf(\"a!\\n\");"                                                     +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "int main(){"                                                          +"\n"+
	            "	a();"                                                                +"\n"+
	            "	printf(\"hello world!\\n\");"                                           +"\n"+
	            "	return 0;"                                                           +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "Graph {"                                                        +"\n"+
	                "  a_0_2"                                        +"\n"+
	                "  c_0_1"                                        +"\n"+
	                "  main_0_3"                                        +"\n"+
	                "  b_0_0"                                        +"\n"+
	                "  main_0_3 -> a_0_2"                                        +"\n"+
	            "}"
	            ,
	            },
/////////////////  5   ///////////////////	
	            {
	            "#include <stdio.h>"                                                   +"\n"+
	            "int i=0;"                                                             +"\n"+
	            ""                                                                     +"\n"+
	            "int c(){	"                                                            +"\n"+
	            "	return 0;"                                                           +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "void b(int i){"                                                       +"\n"+
	            "	printf(\"b!\\n\");"                                                     +"\n"+
	            "}"                                                                    +"\n"+
	            "void a(){}"                                                           +"\n"+
	            ""                                                                     +"\n"+
	            "int main(){	"                                                         +"\n"+
	            "	a();"                                                                +"\n"+
	            "	b(c);"                                                               +"\n"+
	            "	printf(\"hello world!\\n\");"                                           +"\n"+
	            "	return 0;"                                                           +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "Graph {"                                                        +"\n"+
	                "  a_0_3"                                        +"\n"+
	                "  main_0_1"                                        +"\n"+
	                "  c_0_2"                                        +"\n"+
	                "  b_1_0"                                        +"\n"+
	                "  main_0_1 -> a_0_3"                                        +"\n"+
	                "  main_0_1 -> c_0_2"                                        +"\n"+
	                "  main_0_1 -> b_1_0"                                        +"\n"+
	            "}"
	            ,
	            },
/////////////////  6   ///////////////////	
	            {
	            "#include <stdio.h>"                                                   +"\n"+
	            "int c(){	"                                                            +"\n"+
	            "	return 0;"                                                           +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "void a(){}"                                                           +"\n"+
	            ""                                                                     +"\n"+
	            "int main(){	"                                                         +"\n"+
	            "	int i = c();"                                                        +"\n"+
	            "	a();"                                                                +"\n"+
	            "	"                                                                    +"\n"+
	            "	printf(\"hello world!\\n\");"                                           +"\n"+
	            "	return 0;"                                                           +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "Graph {"                                                        +"\n"+
	                "  main_0_1"                                        +"\n"+
	                "  a_0_2"                                        +"\n"+
	                "  c_0_0"                                        +"\n"+
	                "  main_0_1 -> a_0_2"                                        +"\n"+
	                "  main_0_1 -> c_0_0"                                        +"\n"+
	            "}"
	            ,
	            },
/////////////////  7   ///////////////////	
	            {
	            "void*f();"                                                            +"\n"+
	            "void p(){}"                                                           +"\n"+
	            "void m()"                                                             +"\n"+
	            "{"                                                                    +"\n"+
	            "	F=&p;"                                                               +"\n"+
	            "	F();"                                                                +"\n"+
	            "	f();"                                                                +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "Graph {"                                                        +"\n"+
	                "  p_0_0"                                        +"\n"+
	                "  m_0_1"                                        +"\n"+
	                "  m_0_1 -> p_0_0"                                        +"\n"+
	            "}"
	            ,
	            },
	
		});
	}
}
		