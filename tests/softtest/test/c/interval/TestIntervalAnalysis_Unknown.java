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
public class TestIntervalAnalysis_Unknown {

	private String source = null;
	private String vexstr = null;
	private String varstr =null;
	private String valuestr=null;
	private String domainstr=null;

	public TestIntervalAnalysis_Unknown(String source, String vexstr, String varstr, String valuestr, String domainstr) {
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
		
//		assertEquals("interval analyssi error",valuestr,value);
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
	
	@Parameters
	public static Collection<Object[]> testcaseAndResults(){
		return Arrays.asList(new Object[][] {
				
/////////////////  1  unknown-参数   ///////////////////	
	            {
	            "void f(int m,int *p){"                                                +"\n"+
	            "int a[m];"                                                            +"\n"+
	            "int *q=p;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "decl_stmt_1"
	            ,
	            "a"
	            ,
	            "S_45"
	            ,
	            "NOTNULL offsetRange: emptydomain Eval: [0,0] Type:[Stack]"
	            ,
	            },
/////////////////  2    unknown-参数  ///////////////////	
	            {
	            "void npd_gen_must(int flag, char *arg){"                              +"\n"+
	            "char *p = arg;"                                                       +"\n"+
	            "if (flag) p = 0;"                                                     +"\n"+
	            "if (arg) {;}"                                                         +"\n"+
	            "xstrcpy(p,\"Hello\");"                                           +"\n"+
	            "int c[5]={1,2,3,4,5};"                                                +"\n"+
	            "p=c;"                                                                 +"\n"+
	            "}"                                                                    
	            ,
	            "if_head_5"
	            ,
	            "p"
	            ,
	            "arg_01"
	            ,
	            "unknown"
	            ,
	            },

 /////////////////  3   unknown-参数-if  ///////////////////	
	            {
	            "void f(int m){"                                                       +"\n"+
	            "if(m>6)"                                                              +"\n"+
	            "int a=6;"                                                             +"\n"+
	            "else "                                                                +"\n"+
	            "int b=7;"                                                             +"\n"+
	            "int c=8;"                                                             +"\n"+
	            "}"                                                                    
	            ,
	            "if_out_4"
	            ,
	            "m"
	            ,
	            "m_01"
	            ,
	            "[-inf,inf]"
	            ,
	            },
///////////////// 4   unknown-参数-if (注意：if两个分支都不是不可达，因为unknown和unknown无法比较)///////////////////	
	            {
	            "void f(int m,int *p){"                                                +"\n"+
	            "int a[m];"                                                            +"\n"+
	            "int *q=p;"                                                            +"\n"+
	            "if(p==q)"                                                             +"\n"+
	            ";"                                                                    +"\n"+
	            "}"                                                                    
	            ,
	            "if_out_5"
	            ,
	            "p"
	            ,
	            "p_01"
	            ,
	            "unknown"
	            ,
	            },
/////////////////  5   unknown-参数-if (注意：if两个分支都不是不可达，因为unknown和unknown无法比较)   ///////////////////	
	            {
	            "void f(int m,int n){"                                                 +"\n"+
	            "if(m>n)"                                                              +"\n"+
	            ";"                                                                    +"\n"+
	            "}"                                                                    
	            ,
	            "if_head_1"
	            ,
	            "m"
	            ,
	            "m_23"
	            ,
	            "unknown"
	            ,
	            },
/////////////////  6   ///////////////////	
	            {
	            "int f(int m){"                                                        +"\n"+
	            "int a=m+3;"                                                           +"\n"+
	            "}"                                                                    
	            ,
	            "decl_stmt_1"
	            ,
	            "a"
	            ,
	            "3+m_01"
	            ,
	            "unknown"
	            ,
	            },            
 
				
		});
	}
}