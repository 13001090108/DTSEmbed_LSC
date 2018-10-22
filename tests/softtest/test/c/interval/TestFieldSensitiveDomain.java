package softtest.test.c.interval;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;
import java.io.*;
import java.util.*;
import org.junit.*;
import org.junit.runner.*;
import org.junit.runners.*;
import org.junit.runners.Parameterized.*;
import softtest.ast.c.*;
import softtest.cfg.c.*;
import softtest.config.c.Config;
import softtest.domain.c.analysis.*;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.symbolic.Expression;
import softtest.domain.c.symbolic.SymbolFactor;
import softtest.symboltable.c.*;
import softtest.tools.c.jaxen.MatchesFunction;

@RunWith(Parameterized.class)
public class TestFieldSensitiveDomain
{
	private String source = null;
	private String vexstr = null;
	private String varstr =null;
	private String valuestr=null;
	private String domainstr=null;

	public TestFieldSensitiveDomain(String source, String vexstr, String varstr, String valuestr, String domainstr) {
		this.source = source;
		this.vexstr = vexstr;
		this.varstr = varstr;
		this.valuestr = valuestr;
		this.domainstr = domainstr;
	}

	@BeforeClass
	public static void setUpBase()  {
		//注册Xpath中的Matches方法，当前由于不支持Xpath2.0所以Matches要手工实现，并注册
		MatchesFunction.registerSelfInSimpleContext();
		Config.REGRESS_RULE_TEST=true;
		Config.Field=true;
	}

	@AfterClass
	public static void tearDownBase() {
	}
	
	private void analysis(ASTTranslationUnit astroot){
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
		
		assertEquals("interval analyssi error",domainstr,domain);
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
	
		CParser.setType("gcc");
		try {
			gcc_astroot = parser_gcc.TranslationUnit();
		} catch (ParseException e) {
			e.printStackTrace();
			fail("parse error");
		}
		analysis(gcc_astroot);
	}
	
	@Parameters
	public static Collection<Object[]> testcaseAndResults(){
		return Arrays.asList(new Object[][] {
/////////////////  0   ///////////////////	
	            {
	            "struct str{"                                                          +"\n"+
	            "int a;"                                                               +"\n"+
	            "int b;"                                                               +"\n"+
	            "};"                                                                   +"\n"+
	            "void f( ){"                                                           +"\n"+
	            "struct str s;"                                                        +"\n"+
	            "s.a=10;"                                                              +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_2"
	            ,
	            "s.a"
	            ,
	            "10"
	            ,
	            "[10,10]"
	            ,
	            },
/////////////////  1   ///////////////////	
	            {
	            "struct str{"                                                          +"\n"+
	            "int a;"                                                               +"\n"+
	            "int b;"                                                               +"\n"+
	            "};"                                                                   +"\n"+
	            "void f( ){"                                                           +"\n"+
	            "struct str s;"                                                        +"\n"+
	            "s.a=10;"                                                              +"\n"+
	            "int b=1+s.a;"                                                         +"\n"+
	            "}"                                                                    
	            ,
	            "decl_stmt_3"
	            ,
	            "b"
	            ,
	            "11"
	            ,
	            "[11,11]"
	            ,
	            },
/////////////////  2   ///////////////////	
	            {
	            "struct str{"                                                          +"\n"+
	            "int a;"                                                               +"\n"+
	            "int b;"                                                               +"\n"+
	            "};"                                                                   +"\n"+
	            "void f( ){"                                                           +"\n"+
	            "struct str s;"                                                        +"\n"+
	            "s.a=10;"                                                              +"\n"+
	            "int b=s.a*2;"                                                         +"\n"+
	            "}"                                                                    
	            ,
	            "decl_stmt_3"
	            ,
	            "b"
	            ,
	            "20"
	            ,
	            "[20,20]"
	            ,
	            },
/////////////////  3   ///////////////////	
	            {
	            "struct str{"                                                          +"\n"+
	            "int a;"                                                               +"\n"+
	            "int b;"                                                               +"\n"+
	            "};"                                                                   +"\n"+
	            "void f( ){"                                                           +"\n"+
	            "struct str s;"                                                        +"\n"+
	            "s.a=10;"                                                              +"\n"+
	            "int b=s.a++;"                                                         +"\n"+
	            "}"                                                                    
	            ,
	            "decl_stmt_3"
	            ,
	            "b"
	            ,
	            "10"
	            ,
	            "[10,10]"
	            ,
	            },
/////////////////  4   ///////////////////	
	            {
	            "struct str{"                                                          +"\n"+
	            "int a;"                                                               +"\n"+
	            "int b;"                                                               +"\n"+
	            "};"                                                                   +"\n"+
	            "void f( ){"                                                           +"\n"+
	            "struct str s;"                                                        +"\n"+
	            "s.a=10;"                                                              +"\n"+
	            "int b=s.a++;"                                                         +"\n"+
	            "}"                                                                    
	            ,
	            "decl_stmt_3"
	            ,
	            "s.a"
	            ,
	            "11"
	            ,
	            "[11,11]"
	            ,
	            },
/////////////////  5   ///////////////////	
	            {
	            "struct str{"                                                          +"\n"+
	            "int a;"                                                               +"\n"+
	            "int b;"                                                               +"\n"+
	            "};"                                                                   +"\n"+
	            "void f( ){"                                                           +"\n"+
	            "struct str s;"                                                        +"\n"+
	            "s.a=10;"                                                              +"\n"+
	            "int b=++s.a;"                                                         +"\n"+
	            "}"                                                                    
	            ,
	            "decl_stmt_3"
	            ,
	            "b"
	            ,
	            "11"
	            ,
	            "[11,11]"
	            ,
	            },
/////////////////  6   ///////////////////	
	            {
	            "struct str{"                                                          +"\n"+
	            "int a;"                                                               +"\n"+
	            "int b;"                                                               +"\n"+
	            "};"                                                                   +"\n"+
	            "void f(){"                                                            +"\n"+
	            "struct str s1;"                                                       +"\n"+
	            "s1.a=2;"                                                              +"\n"+
	            "s1.a*=5;"                                                             +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_3"
	            ,
	            "s1.a"
	            ,
	            "10"
	            ,
	            "[10,10]"
	            ,
	            },

/////////////////  7   ///////////////////	
	            {
	            "struct str{"                                                          +"\n"+
	            "int a;"                                                               +"\n"+
	            "int b;"                                                               +"\n"+
	            "};"                                                                   +"\n"+
	            "void f( ){"                                                           +"\n"+
	            "struct str s1,s2;"                                                    +"\n"+
	            "s1.a=10;"                                                             +"\n"+
	            "s2.b=5;"                                                              +"\n"+
	            "int b=s1.a+s2.b;"                                                     +"\n"+
	            "}"                                                                    
	            ,
	            "decl_stmt_4"
	            ,
	            "b"
	            ,
	            "15"
	            ,
	            "[15,15]"
	            ,
	            },
/////////////////  8   ///////////////////	
	            {
	            "struct str{"                                                          +"\n"+
	            "int a;"                                                               +"\n"+
	            "int b;"                                                               +"\n"+
	            "};"                                                                   +"\n"+
	            "void f( ){"                                                           +"\n"+
	            "struct str s1,s2;"                                                    +"\n"+
	            "s1.a=10;"                                                             +"\n"+
	            "s2.b=5;"                                                              +"\n"+
	            "int b=s1.a/s2.b;"                                                     +"\n"+
	            "}"                                                                    
	            ,
	            "decl_stmt_4"
	            ,
	            "b"
	            ,
	            "2.0"
	            ,
	            "[2,2]"
	            ,
	            },
/////////////////  9   ///////////////////	
	            {
	            "struct str{"                                                          +"\n"+
	            "int a;"                                                               +"\n"+
	            "int b;"                                                               +"\n"+
	            "};"                                                                   +"\n"+
	            "void f(int i){"                                                       +"\n"+
	            "struct str s1;"                                                       +"\n"+
	            "if(i>0)"                                                              +"\n"+
	            "s1.a=10;"                                                             +"\n"+
	            "else"                                                                 +"\n"+
	            "s1.a=5;"                                                              +"\n"+
	            ""                                                                     +"\n"+
	            "}"                                                                    
	            ,
	            "if_out_5"
	            ,
	            "s1.a"
	            ,
	            "s1.a_1213"
	            ,
	            "[5,5]U[10,10]"
	            ,
	            },
/////////////////  10   ///////////////////	
	            {
	            "struct a{"                                                            +"\n"+
	            "int a;"                                                               +"\n"+
	            "};"                                                                   +"\n"+
	            "struct b{"                                                            +"\n"+
	            "int a;"                                                               +"\n"+
	            "struct b;"                                                            +"\n"+
	            "};"                                                                   +"\n"+
	            "void f(){"                                                            +"\n"+
	            "struct b test;"                                                       +"\n"+
	            "test.a=2;"                                                            +"\n"+
	            "test.b.a=10;"                                                         +"\n"+
	            "int re=test.a*test.b.a;"                                              +"\n"+
	            "}"                                                                    
	            ,
	            "decl_stmt_4"
	            ,
	            "re"
	            ,
	            "20"
	            ,
	            "[20,20]"
	            ,
	            },
/////////////////  11   ///////////////////	
	            {
	            "struct str1{"                                                         +"\n"+
	            "int a;"                                                               +"\n"+
	            "int *p;"                                                              +"\n"+
	            "};"                                                                   +"\n"+
	            "struct str2{"                                                         +"\n"+
	            "int a;"                                                               +"\n"+
	            "struct str1 b;"                                                       +"\n"+
	            "};"                                                                   +"\n"+
	            "void f(){"                                                            +"\n"+
	            "struct str2 test;"                                                    +"\n"+
	            "int i=10;"                                                            +"\n"+
	            "test.b.p=&i;"                                                         +"\n"+
	            ""                                                                     +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_3"
	            ,
	            "test.b.p"
	            ,
	            "S_01"
	            ,
	            "NOTNULL offsetRange: [0,0] Eval: [0,0] Type:[Stack]"
	            ,
	            },
/////////////////  12   ///////////////////	
	            {
	            "struct str1{"                                                         +"\n"+
	            "int a;"                                                               +"\n"+
	            "int* p;"                                                              +"\n"+
	            "};"                                                                   +"\n"+
	            "struct str2{"                                                         +"\n"+
	            "int a;"                                                               +"\n"+
	            "struct str1 b;"                                                       +"\n"+
	            "};"                                                                   +"\n"+
	            "void f(){"                                                            +"\n"+
	            "int a;"                                                               +"\n"+
	            "struct str2* s=(struct str2*)malloc(sizeof(struct str2));"            +"\n"+
	            "s->a=10;"                                                             +"\n"+
	            "s->b.a=++s->a;"                                                       +"\n"+
	            "}"                                                                    
	            ,
	            "stmt_4"
	            ,
	            "s->b.a"
	            ,
	            "11"
	            ,
	            "[11,11]"
	            ,
	            },


		});
	}
}
