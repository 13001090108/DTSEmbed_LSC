package softtest.test.c.symboltable;


import static org.junit.Assert.*;

import java.io.*;
import java.util.*;

import softtest.ast.c.*;
import softtest.symboltable.c.*;
import softtest.tools.c.jaxen.*;

import org.jaxen.JaxenException;
import org.junit.*;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;


@RunWith(Parameterized.class)
public class TestScopeAndDeclarationFinder_static_extern{
	private String source = null;
	private String compiletype=null;
	private String expr = null;
	private String isextern = null;
	private String isstatic = null;
	
	public TestScopeAndDeclarationFinder_static_extern(String source,String compiletype, String expr, String isextern,String isstatic) {
		this.source = source;
		this.compiletype=compiletype;
		this.expr = expr;
		this.isextern = isextern;
		this.isstatic = isstatic;
	}

	@BeforeClass
	public static void setUpBase()  {
		//注册Xpath中的Matches方法，当前由于不支持Xpath2.0所以Matches要手工实现，并注册
		MatchesFunction.registerSelfInSimpleContext();
	}

	@AfterClass
	public static void tearDownBase() {
	}
	
	
	
	private void analysis(ASTTranslationUnit astroot){
		astroot.jjtAccept(new ScopeAndDeclarationFinder(), null);
		List eval = null;
		try {
			eval = astroot.findChildNodesWithXPath(expr);
		} catch (JaxenException e) {
			assertEquals("the xpath parameter expr is not valid", 0, 1);
		}
		
		if (eval == null || eval.size() < 1) {
			assertEquals("cannot find the node matched with the xpath", 0, 1);
		}
		
		for (Object obj : eval) {
			SimpleNode eb = (SimpleNode) obj;
			VariableNameDeclaration  v = eb.getVariableNameDeclaration();
			String isextern = "is not extern", isstatic = "is not static";
			if(v!=null){
				if(v.isExtern())
					isextern = "is extern";
				if(v.isStatic())
					isstatic = "is static";
			}
			assertEquals(""+CParser.getType()+" type error",isextern,this.isextern);
			assertEquals(""+CParser.getType()+" type error",isstatic,this.isstatic);
			break;
		}
	}

	@Before
	public void init() {
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
	public static Collection<Object[]> testcaseAndResults(){
		return Arrays.asList(new Object[][] {
/////////////////  0   ///////////////////	
	            {
	            "int i;"                                                               
	            ,
	            "all"
	            ,
	            "//Declarator"
	            ,
	            "is not extern"
	            ,
	            "is not static"
	            ,
	            },
/////////////////  1   ///////////////////	
	            {
	            "static int i;"                                                               
	            ,
	            "all"
	            ,
	            "//Declarator"
	            ,
	            "is not extern"
	            ,
	            "is static"
	            ,
	            },
/////////////////  2   ///////////////////	
	            {
	            "static extern int i,j;"                                                               
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='j']"
	            ,
	            "is extern"
	            ,
	            "is static"
	            ,
	            },
/////////////////  3   ///////////////////	
	            {
	            " extern int i;"                                                               
	            ,
	            "all"
	            ,
	            "//Declarator"
	            ,
	            "is extern"
	            ,
	            "is not static"
	            ,
	            },
/////////////////  4   ///////////////////	
	            {
	            "extern static int i;"                                                               
	            ,
	            "all"
	            ,
	            "//Declarator"
	            ,
	            "is extern"
	            ,
	            "is static"
	            ,
	            },
		 }
		);
	}
}