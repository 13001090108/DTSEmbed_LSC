package softtest.test.c.cfg;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.io.ByteArrayInputStream;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.Collection;
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
import softtest.cfg.c.ControlFlowVisitor;
import softtest.cfg.c.Graph;
import softtest.symboltable.c.OccurrenceAndExpressionTypeFinder;
import softtest.symboltable.c.ScopeAndDeclarationFinder;
import softtest.symboltable.c.Type.CType;
import softtest.tools.c.jaxen.MatchesFunction;

@RunWith(Parameterized.class)
public class TestControlFlowVisitor
{
	private String source = null;
	private String compiletype=null;
	private String expr = null;
	private String graphStr = null;
	
	public TestControlFlowVisitor(String source,String compiletype, String expr, String graphStr) {
		this.source = source;
		this.compiletype=compiletype;
		this.expr = expr;
		this.graphStr = graphStr;
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
		astroot.jjtAccept(new OccurrenceAndExpressionTypeFinder(), null);
		astroot.jjtAccept(new ControlFlowVisitor(), null);
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
			Method m;
			String graphString="";
			try {
				m = eb.getClass().getMethod("getGraph");
				if(m!=null){
					Graph g=(Graph) m.invoke(eb);
					if(g!=null){
						graphString=g.toString();
					}
				}
			} catch (Exception e) {
				e.printStackTrace();
			} 		
			assertEquals(""+CParser.getType()+" type error",graphStr,graphString);
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
			    /////////////////    0   ///////////////////	
	            {
	                "main() {"                                                             +"\n"+
	                "int i;"                                                               +"\n"+
	                "int a = 1;"                                                           +"\n"+
	                "for(i=0;i<6;i++)"                                                     +"\n"+
	                "{"                                                                    +"\n"+
	                " a++;"                                                                +"\n"+
	                " (a>i)?a:i;"                                                          +"\n"+
	                "}"                                                                    +"\n"+
	                "}"                                                                    
	                ,
	                "all"
	                ,
	                "//FunctionDefinition"
	                ,
	                "Graph {"                                                        +"\n"+
	                    "  0:func_head_main_0"                                        +"\n"+
	                    "  1:decl_stmt_1"                                        +"\n"+
	                    "  2:decl_stmt_2"                                        +"\n"+
	                    "  3:for_init_3"                                        +"\n"+
	                    "  4:for_head_4"                                        +"\n"+
	                    "  5:stmt_5"                                        +"\n"+
	                    "  6:stmt_6"                                        +"\n"+
	                    "  7:for_inc_7"                                        +"\n"+
	                    "  8:for_out_8"                                        +"\n"+
	                    "  9:func_out_main_9"                                        +"\n"+
	                    "  0-0->1"                                        +"\n"+
	                    "  1-1->2"                                        +"\n"+
	                    "  2-2->3"                                        +"\n"+
	                    "  3-3->4"                                        +"\n"+
	                    "  4-T_4->5"                                        +"\n"+
	                    "  5-5->6"                                        +"\n"+
	                    "  6-6->7"                                        +"\n"+
	                    "  7-7->4"                                        +"\n"+
	                    "  4-F_8->8"                                        +"\n"+
	                    "  8-9->9"                                        +"\n"+
	                "}"
	                ,
	                },
	        	    /////////////////    1   /////////////////////////////////	
	                {
	                    "main() {"                                                             +"\n"+
	                    "int count = 1;"                                                       +"\n"+
	                    "if (count>10) {"                                                      +"\n"+
	                    "	goto end;"                                                           +"\n"+
	                    "}"                                                                    +"\n"+
	                    "end: "                                                                +"\n"+
	                    "	count++;"                                                            +"\n"+
	                    "}"                                                                    
	                    ,
	                    "all"
	                    ,
	                    "//FunctionDefinition"
	                    ,
	                    "Graph {"                                                        +"\n"+
	                        "  0:func_head_main_0"                                        +"\n"+
	                        "  1:decl_stmt_1"                                        +"\n"+
	                        "  2:if_head_2"                                        +"\n"+
	                        "  3:goto_3"                                        +"\n"+
	                        "  4:if_out_4"                                        +"\n"+
	                        "  5:label_head_end_5"                                        +"\n"+
	                        "  6:stmt_6"                                        +"\n"+
	                        "  7:func_out_main_7"                                        +"\n"+
	                        "  0-0->1"                                        +"\n"+
	                        "  1-1->2"                                        +"\n"+
	                        "  2-T_2->3"                                        +"\n"+
	                        "  2-F_3->4"                                        +"\n"+
	                        "  4-4->5"                                        +"\n"+
	                        "  5-5->6"                                        +"\n"+
	                        "  6-6->7"                                        +"\n"+
	                        "  3-7->5"                                        +"\n"+
	                    "}"
	                    ,
	                    },
	    /////////////////  2   ///////////////////	
	                    {
	                    "int main()"                                                           +"\n"+
	                    "{"                                                                    +"\n"+
	                    "	__label__ label;"                                                    +"\n"+
	                    "	void *ptr=&&label;"                                                  +"\n"+
	                    "	int i=1;"                                                            +"\n"+
	                    "	if(i==1){"                                                           +"\n"+
	                    "		i=2;"                                                               +"\n"+
	                    "		goto *ptr;"                                                         +"\n"+
	                    "	}"                                                                   +"\n"+
	                    "	i=0;"                                                                +"\n"+
	                    "	label:"                                                              +"\n"+
	                    "		i++;"                                                               +"\n"+
	                    "	printf(\"%d\\n\",i);"                                                   +"\n"+
	                    "	return 0;"                                                           +"\n"+
	                    "}"                                                                    
	                    ,
	                    "gcc"
	                    ,
	                    "//FunctionDefinition"
	                    ,
	                    "Graph {"                                                        +"\n"+
	                        "  0:func_head_main_0"                                        +"\n"+
	                        "  1:label_decl_stmt_1"                                        +"\n"+
	                        "  2:decl_stmt_2"                                        +"\n"+
	                        "  3:decl_stmt_3"                                        +"\n"+
	                        "  4:if_head_4"                                        +"\n"+
	                        "  5:stmt_5"                                        +"\n"+
	                        "  6:goto_6"                                        +"\n"+
	                        "  7:if_out_7"                                        +"\n"+
	                        "  8:stmt_8"                                        +"\n"+
	                        "  9:label_head_label_9"                                        +"\n"+
	                        "  10:stmt_10"                                        +"\n"+
	                        "  11:stmt_11"                                        +"\n"+
	                        "  12:return_12"                                        +"\n"+
	                        "  13:func_out_main_13"                                        +"\n"+
	                        "  0-0->1"                                        +"\n"+
	                        "  1-1->2"                                        +"\n"+
	                        "  2-2->3"                                        +"\n"+
	                        "  3-3->4"                                        +"\n"+
	                        "  4-T_4->5"                                        +"\n"+
	                        "  5-5->6"                                        +"\n"+
	                        "  4-F_6->7"                                        +"\n"+
	                        "  7-7->8"                                        +"\n"+
	                        "  8-8->9"                                        +"\n"+
	                        "  9-9->10"                                        +"\n"+
	                        "  10-10->11"                                        +"\n"+
	                        "  11-11->12"                                        +"\n"+
	                        "  12-12->13"                                        +"\n"+
	                        "  6-13->9"                                        +"\n"+
	                    "}"
	                    ,
	                    },


	    /////////////////  3   ///////////////////	
	                    {
	                    "main() {"                                                             +"\n"+
	                    "int count = 1;"                                                       +"\n"+
	                    "if (count>10) {"                                                      +"\n"+
	                    "	goto end;"                                                           +"\n"+
	                    "}"                                                                    +"\n"+
	                    "end:"                                                                 +"\n"+
	                    "	return 0;"                                                           +"\n"+
	                    "}"                                                                    
	                    ,
	                    "all"
	                    ,
	                    "//FunctionDefinition"
	                    ,
	                    "Graph {"                                                        +"\n"+
	                        "  0:func_head_main_0"                                        +"\n"+
	                        "  1:decl_stmt_1"                                        +"\n"+
	                        "  2:if_head_2"                                        +"\n"+
	                        "  3:goto_3"                                        +"\n"+
	                        "  4:if_out_4"                                        +"\n"+
	                        "  5:label_head_end_5"                                        +"\n"+
	                        "  6:return_6"                                        +"\n"+
	                        "  7:func_out_main_7"                                        +"\n"+
	                        "  0-0->1"                                        +"\n"+
	                        "  1-1->2"                                        +"\n"+
	                        "  2-T_2->3"                                        +"\n"+
	                        "  2-F_3->4"                                        +"\n"+
	                        "  4-4->5"                                        +"\n"+
	                        "  5-5->6"                                        +"\n"+
	                        "  6-6->7"                                        +"\n"+
	                        "  3-7->5"                                        +"\n"+
	                    "}"
	                    ,
	                    },

	    /////////////////  4   ///////////////////	
	                    {
	                    "#include<stdio.h>"                                                    +"\n"+
	                    ""                                                                     +"\n"+
	                    "main() {"                                                             +"\n"+
	                    "int count = 1;"                                                       +"\n"+
	                    "start:"                                                               +"\n"+
	                    "if (count>10) {"                                                      +"\n"+
	                    "	goto end;"                                                           +"\n"+
	                    "}"                                                                    +"\n"+
	                    "	printf(\"%d \", count);"                                               +"\n"+
	                    "	count ++;"                                                           +"\n"+
	                    "	goto start;"                                                         +"\n"+
	                    ""                                                                     +"\n"+
	                    "end:"                                                                 +"\n"+
	                    "	putchar('\\n');"                                                      +"\n"+
	                    "	return 0;"                                                           +"\n"+
	                    "}"                                                                    
	                    ,
	                    "all"
	                    ,
	                    "//FunctionDefinition"
	                    ,
	                    "Graph {"                                                        +"\n"+
	                        "  0:func_head_main_0"                                        +"\n"+
	                        "  1:decl_stmt_1"                                        +"\n"+
	                        "  2:label_head_start_2"                                        +"\n"+
	                        "  3:if_head_3"                                        +"\n"+
	                        "  4:goto_4"                                        +"\n"+
	                        "  5:if_out_5"                                        +"\n"+
	                        "  6:stmt_6"                                        +"\n"+
	                        "  7:stmt_7"                                        +"\n"+
	                        "  8:goto_8"                                        +"\n"+
	                        "  9:label_head_end_9"                                        +"\n"+
	                        "  10:stmt_10"                                        +"\n"+
	                        "  11:return_11"                                        +"\n"+
	                        "  12:func_out_main_12"                                        +"\n"+
	                        "  0-0->1"                                        +"\n"+
	                        "  1-1->2"                                        +"\n"+
	                        "  2-2->3"                                        +"\n"+
	                        "  3-T_3->4"                                        +"\n"+
	                        "  3-F_4->5"                                        +"\n"+
	                        "  5-5->6"                                        +"\n"+
	                        "  6-6->7"                                        +"\n"+
	                        "  7-7->8"                                        +"\n"+
	                        "  9-8->10"                                        +"\n"+
	                        "  10-9->11"                                        +"\n"+
	                        "  11-10->12"                                        +"\n"+
	                        "  4-11->9"                                        +"\n"+
	                        "  8-12->2"                                        +"\n"+
	                    "}"
	                    ,
	                    },

	    /////////////////  5   ///////////////////	
	                    {
	                    "main() {"                                                             +"\n"+
	                    "int count = 1;"                                                       +"\n"+
	                    "}"                                                                    
	                    ,
	                    "all"
	                    ,
	                    "//FunctionDefinition"
	                    ,
	                    "Graph {"                                                        +"\n"+
	                        "  0:func_head_main_0"                                        +"\n"+
	                        "  1:decl_stmt_1"                                        +"\n"+
	                        "  2:func_out_main_2"                                        +"\n"+
	                        "  0-0->1"                                        +"\n"+
	                        "  1-1->2"                                        +"\n"+
	                    "}"
	                    ,
	                    },
	    /////////////////  6   ///////////////////	
	                    {
	                    "int main()"                                                           +"\n"+
	                    "{"                                                                    +"\n"+
	                    "	__label__ label;"                                                    +"\n"+
	                    "	void *ptr;"                                                          +"\n"+
	                    "	ptr=&&label;"                                                        +"\n"+
	                    "	int i=1;"                                                            +"\n"+
	                    "	if(i==1){"                                                           +"\n"+
	                    "		i=2;"                                                               +"\n"+
	                    "		goto *ptr;"                                                         +"\n"+
	                    "	}"                                                                   +"\n"+
	                    "	i=0;"                                                                +"\n"+
	                    "	label:"                                                              +"\n"+
	                    "		i++;"                                                               +"\n"+
	                    "	printf(\"%d\\n\",i);"                                                   +"\n"+
	                    "	return 0;"                                                           +"\n"+
	                    "}"                                                                    
	                    ,
	                    "gcc"
	                    ,
	                    "//FunctionDefinition"
	                    ,
	                    "Graph {"                                                        +"\n"+
	                        "  0:func_head_main_0"                                        +"\n"+
	                        "  1:label_decl_stmt_1"                                        +"\n"+
	                        "  2:decl_stmt_2"                                        +"\n"+
	                        "  3:stmt_3"                                        +"\n"+
	                        "  4:decl_stmt_4"                                        +"\n"+
	                        "  5:if_head_5"                                        +"\n"+
	                        "  6:stmt_6"                                        +"\n"+
	                        "  7:goto_7"                                        +"\n"+
	                        "  8:if_out_8"                                        +"\n"+
	                        "  9:stmt_9"                                        +"\n"+
	                        "  10:label_head_label_10"                                        +"\n"+
	                        "  11:stmt_11"                                        +"\n"+
	                        "  12:stmt_12"                                        +"\n"+
	                        "  13:return_13"                                        +"\n"+
	                        "  14:func_out_main_14"                                        +"\n"+
	                        "  0-0->1"                                        +"\n"+
	                        "  1-1->2"                                        +"\n"+
	                        "  2-2->3"                                        +"\n"+
	                        "  3-3->4"                                        +"\n"+
	                        "  4-4->5"                                        +"\n"+
	                        "  5-T_5->6"                                        +"\n"+
	                        "  6-6->7"                                        +"\n"+
	                        "  5-F_7->8"                                        +"\n"+
	                        "  8-8->9"                                        +"\n"+
	                        "  9-9->10"                                        +"\n"+
	                        "  10-10->11"                                        +"\n"+
	                        "  11-11->12"                                        +"\n"+
	                        "  12-12->13"                                        +"\n"+
	                        "  13-13->14"                                        +"\n"+
	                        "  7-14->10"                                        +"\n"+
	                    "}"
	                    ,
	                    },

	    /////////////////  7   ///////////////////	
	                    {
	                    "main() {"                                                             +"\n"+
	                    "int i;"                                                               +"\n"+
	                    "int a = 1;"                                                           +"\n"+
	                    "for(i=0;i<6;i++)"                                                     +"\n"+
	                    "{"                                                                    +"\n"+
	                    "if (i>a) continue;"                                                   +"\n"+
	                    "else break;"                                                          +"\n"+
	                    "}"                                                                    +"\n"+
	                    "return;"                                                              +"\n"+
	                    "}"                                                                    
	                    ,
	                    "all"
	                    ,
	                    "//FunctionDefinition"
	                    ,
	                    "Graph {"                                                        +"\n"+
	                        "  0:func_head_main_0"                                        +"\n"+
	                        "  1:decl_stmt_1"                                        +"\n"+
	                        "  2:decl_stmt_2"                                        +"\n"+
	                        "  3:for_init_3"                                        +"\n"+
	                        "  4:for_head_4"                                        +"\n"+
	                        "  5:if_head_5"                                        +"\n"+
	                        "  6:continue_6"                                        +"\n"+
	                        "  7:break_7"                                        +"\n"+
	                        "  8:for_inc_8"                                        +"\n"+
	                        "  9:for_out_9"                                        +"\n"+
	                        "  10:return_10"                                        +"\n"+
	                        "  11:func_out_main_11"                                        +"\n"+
	                        "  0-0->1"                                        +"\n"+
	                        "  1-1->2"                                        +"\n"+
	                        "  2-2->3"                                        +"\n"+
	                        "  3-3->4"                                        +"\n"+
	                        "  4-T_4->5"                                        +"\n"+
	                        "  5-T_5->6"                                        +"\n"+
	                        "  5-F_6->7"                                        +"\n"+
	                        "  8-7->4"                                        +"\n"+
	                        "  4-F_8->9"                                        +"\n"+
	                        "  7-9->9"                                        +"\n"+
	                        "  6-10->8"                                        +"\n"+
	                        "  9-11->10"                                        +"\n"+
	                        "  10-12->11"                                        +"\n"+
	                    "}"
	                    ,
	                    },
	    /////////////////  8   ///////////////////	
	                    {
	                    "#include<stdio.h>"                                                    +"\n"+
	                    ""                                                                     +"\n"+
	                    "main() {"                                                             +"\n"+
	                    "int i;"                                                               +"\n"+
	                    "int a;"                                                               +"\n"+
	                    "for(i=0;i<6;i++)"                                                     +"\n"+
	                    "{goto e1;}"                                                           +"\n"+
	                    "a=2;"                                                                 +"\n"+
	                    "e1:"                                                                  +"\n"+
	                    "i=10;"                                                                +"\n"+
	                    "}"                                                                    
	                    ,
	                    "all"
	                    ,
	                    "//FunctionDefinition"
	                    ,
	                    "Graph {"                                                        +"\n"+
	                        "  0:func_head_main_0"                                        +"\n"+
	                        "  1:decl_stmt_1"                                        +"\n"+
	                        "  2:decl_stmt_2"                                        +"\n"+
	                        "  3:for_init_3"                                        +"\n"+
	                        "  4:for_head_4"                                        +"\n"+
	                        "  5:goto_5"                                        +"\n"+
	                        "  6:for_inc_6"                                        +"\n"+
	                        "  7:for_out_7"                                        +"\n"+
	                        "  8:stmt_8"                                        +"\n"+
	                        "  9:label_head_e1_9"                                        +"\n"+
	                        "  10:stmt_10"                                        +"\n"+
	                        "  11:func_out_main_11"                                        +"\n"+
	                        "  0-0->1"                                        +"\n"+
	                        "  1-1->2"                                        +"\n"+
	                        "  2-2->3"                                        +"\n"+
	                        "  3-3->4"                                        +"\n"+
	                        "  4-T_4->5"                                        +"\n"+
	                        "  6-5->4"                                        +"\n"+
	                        "  4-F_6->7"                                        +"\n"+
	                        "  7-7->8"                                        +"\n"+
	                        "  8-8->9"                                        +"\n"+
	                        "  9-9->10"                                        +"\n"+
	                        "  10-10->11"                                        +"\n"+
	                        "  5-11->9"                                        +"\n"+
	                    "}"
	                    ,
	                    },
	    /////////////////  9   ///////////////////	
	                    {
	                    "main()"                                                               +"\n"+
	                    "{"                                                                    +"\n"+
	                    "int i;"                                                               +"\n"+
	                    "int a=1;"                                                             +"\n"+
	                    "int b=5;"                                                             +"\n"+
	                    "int c=1;"                                                             +"\n"+
	                    "e2:"                                                                  +"\n"+
	                    "if(true)"                                                             +"\n"+
	                    "{"                                                                    +"\n"+
	                    "	for(i=0;i<6;i++)"                                                    +"\n"+
	                    "		{"                                                                  +"\n"+
	                    "			c=(a>b)?a:b;"                                                      +"\n"+
	                    "			a++;"                                                              +"\n"+
	                    "			if(a<6)"                                                           +"\n"+
	                    "			{continue;"                                                        +"\n"+
	                    "			}"                                                                 +"\n"+
	                    "			else"                                                              +"\n"+
	                    "			{break;}"                                                          +"\n"+
	                    "		}"                                                                  +"\n"+
	                    "}"                                                                    +"\n"+
	                    "else"                                                                 +"\n"+
	                    "	{"                                                                   +"\n"+
	                    "		goto e1;		"                                                         +"\n"+
	                    "		return i;"                                                          +"\n"+
	                    "	}"                                                                   +"\n"+
	                    "e1:"                                                                  +"\n"+
	                    "	c=10;"                                                               +"\n"+
	                    "	goto e2;"                                                            +"\n"+
	                    "}"                                                                    
	                    ,
	                    "all"
	                    ,
	                    "//FunctionDefinition"
	                    ,
	                    "Graph {"                                                        +"\n"+
	                        "  0:func_head_main_0"                                        +"\n"+
	                        "  1:decl_stmt_1"                                        +"\n"+
	                        "  2:decl_stmt_2"                                        +"\n"+
	                        "  3:decl_stmt_3"                                        +"\n"+
	                        "  4:decl_stmt_4"                                        +"\n"+
	                        "  5:label_head_e2_5"                                        +"\n"+
	                        "  6:if_head_6"                                        +"\n"+
	                        "  7:for_init_7"                                        +"\n"+
	                        "  8:for_head_8"                                        +"\n"+
	                        "  9:stmt_9"                                        +"\n"+
	                        "  10:stmt_10"                                        +"\n"+
	                        "  11:if_head_11"                                        +"\n"+
	                        "  12:continue_12"                                        +"\n"+
	                        "  13:break_13"                                        +"\n"+
	                        "  14:for_inc_14"                                        +"\n"+
	                        "  15:for_out_15"                                        +"\n"+
	                        "  16:goto_16"                                        +"\n"+
	                        "  17:return_17"                                        +"\n"+
	                        "  18:if_out_18"                                        +"\n"+
	                        "  19:label_head_e1_19"                                        +"\n"+
	                        "  20:stmt_20"                                        +"\n"+
	                        "  21:goto_21"                                        +"\n"+
	                        "  22:func_out_main_22"                                        +"\n"+
	                        "  0-0->1"                                        +"\n"+
	                        "  1-1->2"                                        +"\n"+
	                        "  2-2->3"                                        +"\n"+
	                        "  3-3->4"                                        +"\n"+
	                        "  4-4->5"                                        +"\n"+
	                        "  5-5->6"                                        +"\n"+
	                        "  6-T_6->7"                                        +"\n"+
	                        "  7-7->8"                                        +"\n"+
	                        "  8-T_8->9"                                        +"\n"+
	                        "  9-9->10"                                        +"\n"+
	                        "  10-10->11"                                        +"\n"+
	                        "  11-T_11->12"                                        +"\n"+
	                        "  11-F_12->13"                                        +"\n"+
	                        "  14-13->8"                                        +"\n"+
	                        "  8-F_14->15"                                        +"\n"+
	                        "  13-15->15"                                        +"\n"+
	                        "  12-16->14"                                        +"\n"+
	                        "  6-F_17->16"                                        +"\n"+
	                        "  15-18->18"                                        +"\n"+
	                        "  18-19->19"                                        +"\n"+
	                        "  19-20->20"                                        +"\n"+
	                        "  20-21->21"                                        +"\n"+
	                        "  17-22->22"                                        +"\n"+
	                        "  21-23->5"                                        +"\n"+
	                        "  16-24->19"                                        +"\n"+
	                    "}"
	                    ,
	                    },
	    /////////////////  10   ///////////////////	
	                    {
	                    "main()"                                                               +"\n"+
	                    "{"                                                                    +"\n"+
	                    "int i;"                                                               +"\n"+
	                    "int a=1;"                                                             +"\n"+
	                    "int b=5;"                                                             +"\n"+
	                    "int c=1;"                                                             +"\n"+
	                    "e2:"                                                                  +"\n"+
	                    "if(true)"                                                             +"\n"+
	                    "{"                                                                    +"\n"+
	                    "	for (i=0;i<10;i++)"                                                  +"\n"+
	                    "for(i=0;i<6;i++)"                                                     +"\n"+
	                    "		{"                                                                  +"\n"+
	                    "			c=(a>b)?a:b;"                                                      +"\n"+
	                    "			a++;"                                                              +"\n"+
	                    "			if(a<6)"                                                           +"\n"+
	                    "			{continue;"                                                        +"\n"+
	                    "			}"                                                                 +"\n"+
	                    "			else"                                                              +"\n"+
	                    "			{break;}"                                                          +"\n"+
	                    "		}"                                                                  +"\n"+
	                    "}"                                                                    +"\n"+
	                    "else"                                                                 +"\n"+
	                    "	{"                                                                   +"\n"+
	                    "		goto e1;		"                                                         +"\n"+
	                    "		return i;"                                                          +"\n"+
	                    "	}"                                                                   +"\n"+
	                    "e1:"                                                                  +"\n"+
	                    "	c=10;"                                                               +"\n"+
	                    "	goto e2;"                                                            +"\n"+
	                    "}"                                                                    
	                    ,
	                    "all"
	                    ,
	                    "//FunctionDefinition"
	                    ,
	                    "Graph {"                                                        +"\n"+
	                        "  0:func_head_main_0"                                        +"\n"+
	                        "  1:decl_stmt_1"                                        +"\n"+
	                        "  2:decl_stmt_2"                                        +"\n"+
	                        "  3:decl_stmt_3"                                        +"\n"+
	                        "  4:decl_stmt_4"                                        +"\n"+
	                        "  5:label_head_e2_5"                                        +"\n"+
	                        "  6:if_head_6"                                        +"\n"+
	                        "  7:for_init_7"                                        +"\n"+
	                        "  8:for_head_8"                                        +"\n"+
	                        "  9:for_init_9"                                        +"\n"+
	                        "  10:for_head_10"                                        +"\n"+
	                        "  11:stmt_11"                                        +"\n"+
	                        "  12:stmt_12"                                        +"\n"+
	                        "  13:if_head_13"                                        +"\n"+
	                        "  14:continue_14"                                        +"\n"+
	                        "  15:break_15"                                        +"\n"+
	                        "  16:for_inc_16"                                        +"\n"+
	                        "  17:for_out_17"                                        +"\n"+
	                        "  18:for_inc_18"                                        +"\n"+
	                        "  19:for_out_19"                                        +"\n"+
	                        "  20:goto_20"                                        +"\n"+
	                        "  21:return_21"                                        +"\n"+
	                        "  22:if_out_22"                                        +"\n"+
	                        "  23:label_head_e1_23"                                        +"\n"+
	                        "  24:stmt_24"                                        +"\n"+
	                        "  25:goto_25"                                        +"\n"+
	                        "  26:func_out_main_26"                                        +"\n"+
	                        "  0-0->1"                                        +"\n"+
	                        "  1-1->2"                                        +"\n"+
	                        "  2-2->3"                                        +"\n"+
	                        "  3-3->4"                                        +"\n"+
	                        "  4-4->5"                                        +"\n"+
	                        "  5-5->6"                                        +"\n"+
	                        "  6-T_6->7"                                        +"\n"+
	                        "  7-7->8"                                        +"\n"+
	                        "  8-T_8->9"                                        +"\n"+
	                        "  9-9->10"                                        +"\n"+
	                        "  10-T_10->11"                                        +"\n"+
	                        "  11-11->12"                                        +"\n"+
	                        "  12-12->13"                                        +"\n"+
	                        "  13-T_13->14"                                        +"\n"+
	                        "  13-F_14->15"                                        +"\n"+
	                        "  16-15->10"                                        +"\n"+
	                        "  10-F_16->17"                                        +"\n"+
	                        "  15-17->17"                                        +"\n"+
	                        "  14-18->16"                                        +"\n"+
	                        "  17-19->18"                                        +"\n"+
	                        "  18-20->8"                                        +"\n"+
	                        "  8-F_21->19"                                        +"\n"+
	                        "  6-F_22->20"                                        +"\n"+
	                        "  19-23->22"                                        +"\n"+
	                        "  22-24->23"                                        +"\n"+
	                        "  23-25->24"                                        +"\n"+
	                        "  24-26->25"                                        +"\n"+
	                        "  21-27->26"                                        +"\n"+
	                        "  25-28->5"                                        +"\n"+
	                        "  20-29->23"                                        +"\n"+
	                    "}"
	                    ,
	                    },
	    /////////////////  11   ///////////////////	
	                    {
	                    "#include <stdio.h>"                                                   +"\n"+
	                    " main(){"                                                             +"\n"+
	                    "  int a=1;"                                                           +"\n"+
	                    "  int b=2;"                                                           +"\n"+
	                    "  switch(a){"                                                         +"\n"+
	                    "  case 1 : a++;break;"                                                +"\n"+
	                    "  case 2 : return b;break;"                                           +"\n"+
	                    "  default: return a;break;}"                                          +"\n"+
	                    "  switch(b){"                                                         +"\n"+
	                    "   case 1 : a++;break;"                                               +"\n"+
	                    "  case 2 : return b;break;"                                           +"\n"+
	                    "  default: return a;break;}"                                          +"\n"+
	                    "}"                                                                    
	                    ,
	                    "all"
	                    ,
	                    "//FunctionDefinition"
	                    ,
	                    "Graph {"                                                        +"\n"+
	                        "  0:func_head_main_0"                                        +"\n"+
	                        "  1:decl_stmt_1"                                        +"\n"+
	                        "  2:decl_stmt_2"                                        +"\n"+
	                        "  3:switch_head_3"                                        +"\n"+
	                        "  4:label_head_case_4"                                        +"\n"+
	                        "  5:stmt_5"                                        +"\n"+
	                        "  6:break_6"                                        +"\n"+
	                        "  7:label_head_case_7"                                        +"\n"+
	                        "  8:return_8"                                        +"\n"+
	                        "  9:break_9"                                        +"\n"+
	                        "  10:label_head_default_10"                                        +"\n"+
	                        "  11:return_11"                                        +"\n"+
	                        "  12:break_12"                                        +"\n"+
	                        "  13:switch_out_13"                                        +"\n"+
	                        "  14:switch_head_14"                                        +"\n"+
	                        "  15:label_head_case_15"                                        +"\n"+
	                        "  16:stmt_16"                                        +"\n"+
	                        "  17:break_17"                                        +"\n"+
	                        "  18:label_head_case_18"                                        +"\n"+
	                        "  19:return_19"                                        +"\n"+
	                        "  20:break_20"                                        +"\n"+
	                        "  21:label_head_default_21"                                        +"\n"+
	                        "  22:return_22"                                        +"\n"+
	                        "  23:break_23"                                        +"\n"+
	                        "  24:switch_out_24"                                        +"\n"+
	                        "  25:func_out_main_25"                                        +"\n"+
	                        "  0-0->1"                                        +"\n"+
	                        "  1-1->2"                                        +"\n"+
	                        "  2-2->3"                                        +"\n"+
	                        "  3-3->4"                                        +"\n"+
	                        "  4-4->5"                                        +"\n"+
	                        "  5-5->6"                                        +"\n"+
	                        "  3-6->7"                                        +"\n"+
	                        "  7-7->8"                                        +"\n"+
	                        "  3-8->10"                                        +"\n"+
	                        "  10-9->11"                                        +"\n"+
	                        "  6-10->13"                                        +"\n"+
	                        "  9-11->13"                                        +"\n"+
	                        "  12-12->13"                                        +"\n"+
	                        "  13-13->14"                                        +"\n"+
	                        "  14-14->15"                                        +"\n"+
	                        "  15-15->16"                                        +"\n"+
	                        "  16-16->17"                                        +"\n"+
	                        "  14-17->18"                                        +"\n"+
	                        "  18-18->19"                                        +"\n"+
	                        "  14-19->21"                                        +"\n"+
	                        "  21-20->22"                                        +"\n"+
	                        "  17-21->24"                                        +"\n"+
	                        "  20-22->24"                                        +"\n"+
	                        "  23-23->24"                                        +"\n"+
	                        "  24-24->25"                                        +"\n"+
	                        "  8-25->25"                                        +"\n"+
	                        "  11-26->25"                                        +"\n"+
	                        "  19-27->25"                                        +"\n"+
	                        "  22-28->25"                                        +"\n"+
	                    "}"
	                    ,
	                    },
	    /////////////////  12   ///////////////////	
	                    {
	                    "#include <stdio.h>"                                                   +"\n"+
	                    " main(){"                                                             +"\n"+
	                    "  int a=1;"                                                           +"\n"+
	                    "  int b=2;"                                                           +"\n"+
	                    "  switch(a){"                                                         +"\n"+
	                    "  case 1 :{switch (b)"                                                +"\n"+
	                    "  case 2:return b;break;}"                                            +"\n"+
	                    "  break;"                                                             +"\n"+
	                    "  default:return a;break; }"                                          +"\n"+
	                    "}"                                                                    
	                    ,
	                    "all"
	                    ,
	                    "//FunctionDefinition"
	                    ,
	                    "Graph {"                                                        +"\n"+
	                        "  0:func_head_main_0"                                        +"\n"+
	                        "  1:decl_stmt_1"                                        +"\n"+
	                        "  2:decl_stmt_2"                                        +"\n"+
	                        "  3:switch_head_3"                                        +"\n"+
	                        "  4:label_head_case_4"                                        +"\n"+
	                        "  5:switch_head_5"                                        +"\n"+
	                        "  6:label_head_case_6"                                        +"\n"+
	                        "  7:return_7"                                        +"\n"+
	                        "  8:switch_out_8"                                        +"\n"+
	                        "  9:break_9"                                        +"\n"+
	                        "  10:break_10"                                        +"\n"+
	                        "  11:label_head_default_11"                                        +"\n"+
	                        "  12:return_12"                                        +"\n"+
	                        "  13:break_13"                                        +"\n"+
	                        "  14:switch_out_14"                                        +"\n"+
	                        "  15:func_out_main_15"                                        +"\n"+
	                        "  0-0->1"                                        +"\n"+
	                        "  1-1->2"                                        +"\n"+
	                        "  2-2->3"                                        +"\n"+
	                        "  3-3->4"                                        +"\n"+
	                        "  4-4->5"                                        +"\n"+
	                        "  5-5->6"                                        +"\n"+
	                        "  6-6->7"                                        +"\n"+
	                        "  5-7->8"                                        +"\n"+
	                        "  8-8->9"                                        +"\n"+
	                        "  3-9->11"                                        +"\n"+
	                        "  11-10->12"                                        +"\n"+
	                        "  9-11->14"                                        +"\n"+
	                        "  10-12->14"                                        +"\n"+
	                        "  13-13->14"                                        +"\n"+
	                        "  14-14->15"                                        +"\n"+
	                        "  7-15->15"                                        +"\n"+
	                        "  12-16->15"                                        +"\n"+
	                    "}"
	                    ,
	                    },
	    /////////////////  13  ///////////////////	
	                    {
	                    "#include <stdio.h>"                                                   +"\n"+
	                    " main(){"                                                             +"\n"+
	                    "  int a=1;"                                                           +"\n"+
	                    "  int b=2;"                                                           +"\n"+
	                    "  switch(a){"                                                         +"\n"+
	                    "  case 1 : a++;break;"                                                +"\n"+
	                    "  case 2 :"                                                           +"\n"+
	                    "  switch (b){"                                                        +"\n"+
	                    "  case 1:return a;break;"                                             +"\n"+
	                    "  case 3:return b;break;"                                             +"\n"+
	                    "  };"                                                                 +"\n"+
	                    "  break;"                                                             +"\n"+
	                    "  default:return a;break;"                                            +"\n"+
	                    "  }"                                                                  +"\n"+
	                    "}"                                                                    
	                    ,
	                    "all"
	                    ,
	                    "//FunctionDefinition"
	                    ,
	                    "Graph {"                                                        +"\n"+
	                        "  0:func_head_main_0"                                        +"\n"+
	                        "  1:decl_stmt_1"                                        +"\n"+
	                        "  2:decl_stmt_2"                                        +"\n"+
	                        "  3:switch_head_3"                                        +"\n"+
	                        "  4:label_head_case_4"                                        +"\n"+
	                        "  5:stmt_5"                                        +"\n"+
	                        "  6:break_6"                                        +"\n"+
	                        "  7:label_head_case_7"                                        +"\n"+
	                        "  8:switch_head_8"                                        +"\n"+
	                        "  9:label_head_case_9"                                        +"\n"+
	                        "  10:return_10"                                        +"\n"+
	                        "  11:break_11"                                        +"\n"+
	                        "  12:label_head_case_12"                                        +"\n"+
	                        "  13:return_13"                                        +"\n"+
	                        "  14:break_14"                                        +"\n"+
	                        "  15:switch_out_15"                                        +"\n"+
	                        "  16:stmt_16"                                        +"\n"+
	                        "  17:break_17"                                        +"\n"+
	                        "  18:label_head_default_18"                                        +"\n"+
	                        "  19:return_19"                                        +"\n"+
	                        "  20:break_20"                                        +"\n"+
	                        "  21:switch_out_21"                                        +"\n"+
	                        "  22:func_out_main_22"                                        +"\n"+
	                        "  0-0->1"                                        +"\n"+
	                        "  1-1->2"                                        +"\n"+
	                        "  2-2->3"                                        +"\n"+
	                        "  3-3->4"                                        +"\n"+
	                        "  4-4->5"                                        +"\n"+
	                        "  5-5->6"                                        +"\n"+
	                        "  3-6->7"                                        +"\n"+
	                        "  7-7->8"                                        +"\n"+
	                        "  8-8->9"                                        +"\n"+
	                        "  9-9->10"                                        +"\n"+
	                        "  8-10->12"                                        +"\n"+
	                        "  12-11->13"                                        +"\n"+
	                        "  8-12->15"                                        +"\n"+
	                        "  11-13->15"                                        +"\n"+
	                        "  14-14->15"                                        +"\n"+
	                        "  15-15->16"                                        +"\n"+
	                        "  16-16->17"                                        +"\n"+
	                        "  3-17->18"                                        +"\n"+
	                        "  18-18->19"                                        +"\n"+
	                        "  6-19->21"                                        +"\n"+
	                        "  17-20->21"                                        +"\n"+
	                        "  20-21->21"                                        +"\n"+
	                        "  21-22->22"                                        +"\n"+
	                        "  10-23->22"                                        +"\n"+
	                        "  13-24->22"                                        +"\n"+
	                        "  19-25->22"                                        +"\n"+
	                    "}"
	                    ,
	                    },
	    /////////////////  14   ///////////////////	
	                    {
	                    "#include<stdio.h>"                                                    +"\n"+
	                    "main()"                                                               +"\n"+
	                    "{"                                                                    +"\n"+
	                    " int grade;"                                                          +"\n"+
	                    " int a=0,b=0;"                                                        +"\n"+
	                    " while((grade=getchar())!=EOF)"                                       +"\n"+
	                    "    switch(grade)"                                                    +"\n"+
	                    "    {"                                                                +"\n"+
	                    "        case 'A':++a;break;"                                          +"\n"+
	                    "        case 'B':++b;break;"                                          +"\n"+
	                    "        default:printf(\"incorrect!\");break;"                          +"\n"+
	                    "    }"                                                                +"\n"+
	                    "}"                                                                    
	                    ,
	                    "all"
	                    ,
	                    "//FunctionDefinition"
	                    ,
	                    "Graph {"                                                        +"\n"+
	                        "  0:func_head_main_0"                                        +"\n"+
	                        "  1:decl_stmt_1"                                        +"\n"+
	                        "  2:decl_stmt_2"                                        +"\n"+
	                        "  3:while_head_3"                                        +"\n"+
	                        "  4:switch_head_4"                                        +"\n"+
	                        "  5:label_head_case_5"                                        +"\n"+
	                        "  6:stmt_6"                                        +"\n"+
	                        "  7:break_7"                                        +"\n"+
	                        "  8:label_head_case_8"                                        +"\n"+
	                        "  9:stmt_9"                                        +"\n"+
	                        "  10:break_10"                                        +"\n"+
	                        "  11:label_head_default_11"                                        +"\n"+
	                        "  12:stmt_12"                                        +"\n"+
	                        "  13:break_13"                                        +"\n"+
	                        "  14:switch_out_14"                                        +"\n"+
	                        "  15:while_out_15"                                        +"\n"+
	                        "  16:func_out_main_16"                                        +"\n"+
	                        "  0-0->1"                                        +"\n"+
	                        "  1-1->2"                                        +"\n"+
	                        "  2-2->3"                                        +"\n"+
	                        "  3-T_3->4"                                        +"\n"+
	                        "  4-4->5"                                        +"\n"+
	                        "  5-5->6"                                        +"\n"+
	                        "  6-6->7"                                        +"\n"+
	                        "  4-7->8"                                        +"\n"+
	                        "  8-8->9"                                        +"\n"+
	                        "  9-9->10"                                        +"\n"+
	                        "  4-10->11"                                        +"\n"+
	                        "  11-11->12"                                        +"\n"+
	                        "  12-12->13"                                        +"\n"+
	                        "  7-13->14"                                        +"\n"+
	                        "  10-14->14"                                        +"\n"+
	                        "  13-15->14"                                        +"\n"+
	                        "  14-16->3"                                        +"\n"+
	                        "  3-F_17->15"                                        +"\n"+
	                        "  15-18->16"                                        +"\n"+
	                    "}"
	                    ,
	                    },
	    /////////////////  15   ///////////////////	
	                    {
	                    "#include<stdio.h>"                                                    +"\n"+
	                    "main()"                                                               +"\n"+
	                    "{"                                                                    +"\n"+
	                    " int grade;"                                                          +"\n"+
	                    " int a=0,b=0;"                                                        +"\n"+
	                    " int i;"                                                              +"\n"+
	                    " for(i=0;i<=5;i++) "                                                  +"\n"+
	                    " {"                                                                   +"\n"+
	                    "   while((grade=getchar())!=EOF)"                                     +"\n"+
	                    "    switch(grade)"                                                    +"\n"+
	                    "    {"                                                                +"\n"+
	                    "        case 'A':++a;break;"                                          +"\n"+
	                    "        case 'B':++b;break;"                                          +"\n"+
	                    "        default:printf(\"incorrect!\");break;"                          +"\n"+
	                    "    }"                                                                +"\n"+
	                    "  }"                                                                  +"\n"+
	                    "}"                                                                    
	                    ,
	                    "all"
	                    ,
	                    "//FunctionDefinition"
	                    ,
	                    "Graph {"                                                        +"\n"+
	                        "  0:func_head_main_0"                                        +"\n"+
	                        "  1:decl_stmt_1"                                        +"\n"+
	                        "  2:decl_stmt_2"                                        +"\n"+
	                        "  3:decl_stmt_3"                                        +"\n"+
	                        "  4:for_init_4"                                        +"\n"+
	                        "  5:for_head_5"                                        +"\n"+
	                        "  6:while_head_6"                                        +"\n"+
	                        "  7:switch_head_7"                                        +"\n"+
	                        "  8:label_head_case_8"                                        +"\n"+
	                        "  9:stmt_9"                                        +"\n"+
	                        "  10:break_10"                                        +"\n"+
	                        "  11:label_head_case_11"                                        +"\n"+
	                        "  12:stmt_12"                                        +"\n"+
	                        "  13:break_13"                                        +"\n"+
	                        "  14:label_head_default_14"                                        +"\n"+
	                        "  15:stmt_15"                                        +"\n"+
	                        "  16:break_16"                                        +"\n"+
	                        "  17:switch_out_17"                                        +"\n"+
	                        "  18:while_out_18"                                        +"\n"+
	                        "  19:for_inc_19"                                        +"\n"+
	                        "  20:for_out_20"                                        +"\n"+
	                        "  21:func_out_main_21"                                        +"\n"+
	                        "  0-0->1"                                        +"\n"+
	                        "  1-1->2"                                        +"\n"+
	                        "  2-2->3"                                        +"\n"+
	                        "  3-3->4"                                        +"\n"+
	                        "  4-4->5"                                        +"\n"+
	                        "  5-T_5->6"                                        +"\n"+
	                        "  6-T_6->7"                                        +"\n"+
	                        "  7-7->8"                                        +"\n"+
	                        "  8-8->9"                                        +"\n"+
	                        "  9-9->10"                                        +"\n"+
	                        "  7-10->11"                                        +"\n"+
	                        "  11-11->12"                                        +"\n"+
	                        "  12-12->13"                                        +"\n"+
	                        "  7-13->14"                                        +"\n"+
	                        "  14-14->15"                                        +"\n"+
	                        "  15-15->16"                                        +"\n"+
	                        "  10-16->17"                                        +"\n"+
	                        "  13-17->17"                                        +"\n"+
	                        "  16-18->17"                                        +"\n"+
	                        "  17-19->6"                                        +"\n"+
	                        "  6-F_20->18"                                        +"\n"+
	                        "  18-21->19"                                        +"\n"+
	                        "  19-22->5"                                        +"\n"+
	                        "  5-F_23->20"                                        +"\n"+
	                        "  20-24->21"                                        +"\n"+
	                    "}"
	                    ,
	                    },
	    /////////////////  16   ///////////////////	
	                    {
	                    "#include<stdio.h>"                                                    +"\n"+
	                    "main()"                                                               +"\n"+
	                    "{"                                                                    +"\n"+
	                    " int grade;"                                                          +"\n"+
	                    " int a=0,b=0,counter = 1;"                                            +"\n"+
	                    " int i;"                                                              +"\n"+
	                    " for(i=0;i<=5;i++) "                                                  +"\n"+
	                    " {"                                                                   +"\n"+
	                    "   do{"                                                               +"\n"+
	                    "   printf(\"do\");"                                                     +"\n"+
	                    "   while((grade=getchar())!=EOF)"                                     +"\n"+
	                    "    {"                                                                +"\n"+
	                    "      switch(grade)"                                                  +"\n"+
	                    "       {"                                                             +"\n"+
	                    "        case 'A':++a;break;"                                          +"\n"+
	                    "        case 'B':++b;break;"                                          +"\n"+
	                    "        default:printf(\"incorrect!\");break;"                          +"\n"+
	                    "        }"                                                            +"\n"+
	                    "     } "                                                              +"\n"+
	                    "    }"                                                                +"\n"+
	                    "   while(++counter<=10);"                                             +"\n"+
	                    "   return 0;"                                                         +"\n"+
	                    "  }"                                                                  +"\n"+
	                    "}"                                                                    
	                    ,
	                    "all"
	                    ,
	                    "//FunctionDefinition"
	                    ,
	                    "Graph {"                                                        +"\n"+
	                        "  0:func_head_main_0"                                        +"\n"+
	                        "  1:decl_stmt_1"                                        +"\n"+
	                        "  2:decl_stmt_2"                                        +"\n"+
	                        "  3:decl_stmt_3"                                        +"\n"+
	                        "  4:for_init_4"                                        +"\n"+
	                        "  5:for_head_5"                                        +"\n"+
	                        "  6:do_while_head_6"                                        +"\n"+
	                        "  7:stmt_7"                                        +"\n"+
	                        "  8:while_head_8"                                        +"\n"+
	                        "  9:switch_head_9"                                        +"\n"+
	                        "  10:label_head_case_10"                                        +"\n"+
	                        "  11:stmt_11"                                        +"\n"+
	                        "  12:break_12"                                        +"\n"+
	                        "  13:label_head_case_13"                                        +"\n"+
	                        "  14:stmt_14"                                        +"\n"+
	                        "  15:break_15"                                        +"\n"+
	                        "  16:label_head_default_16"                                        +"\n"+
	                        "  17:stmt_17"                                        +"\n"+
	                        "  18:break_18"                                        +"\n"+
	                        "  19:switch_out_19"                                        +"\n"+
	                        "  20:while_out_20"                                        +"\n"+
	                        "  21:do_while_out1_21"                                        +"\n"+
	                        "  22:do_while_out2_22"                                        +"\n"+
	                        "  23:return_23"                                        +"\n"+
	                        "  24:for_inc_24"                                        +"\n"+
	                        "  25:for_out_25"                                        +"\n"+
	                        "  26:func_out_main_26"                                        +"\n"+
	                        "  0-0->1"                                        +"\n"+
	                        "  1-1->2"                                        +"\n"+
	                        "  2-2->3"                                        +"\n"+
	                        "  3-3->4"                                        +"\n"+
	                        "  4-4->5"                                        +"\n"+
	                        "  5-T_5->6"                                        +"\n"+
	                        "  6-6->7"                                        +"\n"+
	                        "  7-7->8"                                        +"\n"+
	                        "  8-T_8->9"                                        +"\n"+
	                        "  9-9->10"                                        +"\n"+
	                        "  10-10->11"                                        +"\n"+
	                        "  11-11->12"                                        +"\n"+
	                        "  9-12->13"                                        +"\n"+
	                        "  13-13->14"                                        +"\n"+
	                        "  14-14->15"                                        +"\n"+
	                        "  9-15->16"                                        +"\n"+
	                        "  16-16->17"                                        +"\n"+
	                        "  17-17->18"                                        +"\n"+
	                        "  12-18->19"                                        +"\n"+
	                        "  15-19->19"                                        +"\n"+
	                        "  18-20->19"                                        +"\n"+
	                        "  19-21->8"                                        +"\n"+
	                        "  8-F_22->20"                                        +"\n"+
	                        "  20-23->21"                                        +"\n"+
	                        "  21-T_24->6"                                        +"\n"+
	                        "  21-F_25->22"                                        +"\n"+
	                        "  22-26->23"                                        +"\n"+
	                        "  24-27->5"                                        +"\n"+
	                        "  5-F_28->25"                                        +"\n"+
	                        "  25-29->26"                                        +"\n"+
	                        "  23-30->26"                                        +"\n"+
	                    "}"
	                    ,
	                    },
	    /////////////////  17   ///////////////////	
	                    {
	                    "#include<stdio.h>"                                                    +"\n"+
	                    "main()"                                                               +"\n"+
	                    "{"                                                                    +"\n"+
	                    " int grade;"                                                          +"\n"+
	                    " int a=0,b=0,counter = 1,c=1;"                                        +"\n"+
	                    " int i;"                                                              +"\n"+
	                    "   "                                                                  +"\n"+
	                    "   for(i=0;i<=5;i++)"                                                 +"\n"+
	                    "     {"                                                               +"\n"+
	                    "      switch(grade)"                                                  +"\n"+
	                    "       {"                                                             +"\n"+
	                    "        case 'A': "                                                   +"\n"+
	                    "            while((grade=getchar())!=EOF)"                            +"\n"+
	                    "              {"                                                      +"\n"+
	                    "               switch(c)"                                             +"\n"+
	                    "                {"                                                    +"\n"+
	                    "                  case 1:c++;break;"                                  +"\n"+
	                    "                  case 2:printf(\"c\");break;"                          +"\n"+
	                    "                  default:printf(\"correct\");break;"                   +"\n"+
	                    "                }"                                                    +"\n"+
	                    "               printf(\"for\"); "                                       +"\n"+
	                    "              }  "                                                    +"\n"+
	                    "            break;"                                                   +"\n"+
	                    "        case 'B':c++;"                                                +"\n"+
	                    "           break;"                                                    +"\n"+
	                    "        default:printf(\"incorrect!\");break;"                          +"\n"+
	                    "        }"                                                            +"\n"+
	                    "     } "                                                              +"\n"+
	                    "}"                                                                    
	                    ,
	                    "all"
	                    ,
	                    "//FunctionDefinition"
	                    ,
	                    "Graph {"                                                        +"\n"+
	                        "  0:func_head_main_0"                                        +"\n"+
	                        "  1:decl_stmt_1"                                        +"\n"+
	                        "  2:decl_stmt_2"                                        +"\n"+
	                        "  3:decl_stmt_3"                                        +"\n"+
	                        "  4:for_init_4"                                        +"\n"+
	                        "  5:for_head_5"                                        +"\n"+
	                        "  6:switch_head_6"                                        +"\n"+
	                        "  7:label_head_case_7"                                        +"\n"+
	                        "  8:while_head_8"                                        +"\n"+
	                        "  9:switch_head_9"                                        +"\n"+
	                        "  10:label_head_case_10"                                        +"\n"+
	                        "  11:stmt_11"                                        +"\n"+
	                        "  12:break_12"                                        +"\n"+
	                        "  13:label_head_case_13"                                        +"\n"+
	                        "  14:stmt_14"                                        +"\n"+
	                        "  15:break_15"                                        +"\n"+
	                        "  16:label_head_default_16"                                        +"\n"+
	                        "  17:stmt_17"                                        +"\n"+
	                        "  18:break_18"                                        +"\n"+
	                        "  19:switch_out_19"                                        +"\n"+
	                        "  20:stmt_20"                                        +"\n"+
	                        "  21:while_out_21"                                        +"\n"+
	                        "  22:break_22"                                        +"\n"+
	                        "  23:label_head_case_23"                                        +"\n"+
	                        "  24:stmt_24"                                        +"\n"+
	                        "  25:break_25"                                        +"\n"+
	                        "  26:label_head_default_26"                                        +"\n"+
	                        "  27:stmt_27"                                        +"\n"+
	                        "  28:break_28"                                        +"\n"+
	                        "  29:switch_out_29"                                        +"\n"+
	                        "  30:for_inc_30"                                        +"\n"+
	                        "  31:for_out_31"                                        +"\n"+
	                        "  32:func_out_main_32"                                        +"\n"+
	                        "  0-0->1"                                        +"\n"+
	                        "  1-1->2"                                        +"\n"+
	                        "  2-2->3"                                        +"\n"+
	                        "  3-3->4"                                        +"\n"+
	                        "  4-4->5"                                        +"\n"+
	                        "  5-T_5->6"                                        +"\n"+
	                        "  6-6->7"                                        +"\n"+
	                        "  7-7->8"                                        +"\n"+
	                        "  8-T_8->9"                                        +"\n"+
	                        "  9-9->10"                                        +"\n"+
	                        "  10-10->11"                                        +"\n"+
	                        "  11-11->12"                                        +"\n"+
	                        "  9-12->13"                                        +"\n"+
	                        "  13-13->14"                                        +"\n"+
	                        "  14-14->15"                                        +"\n"+
	                        "  9-15->16"                                        +"\n"+
	                        "  16-16->17"                                        +"\n"+
	                        "  17-17->18"                                        +"\n"+
	                        "  12-18->19"                                        +"\n"+
	                        "  15-19->19"                                        +"\n"+
	                        "  18-20->19"                                        +"\n"+
	                        "  19-21->20"                                        +"\n"+
	                        "  20-22->8"                                        +"\n"+
	                        "  8-F_23->21"                                        +"\n"+
	                        "  21-24->22"                                        +"\n"+
	                        "  6-25->23"                                        +"\n"+
	                        "  23-26->24"                                        +"\n"+
	                        "  24-27->25"                                        +"\n"+
	                        "  6-28->26"                                        +"\n"+
	                        "  26-29->27"                                        +"\n"+
	                        "  27-30->28"                                        +"\n"+
	                        "  22-31->29"                                        +"\n"+
	                        "  25-32->29"                                        +"\n"+
	                        "  28-33->29"                                        +"\n"+
	                        "  29-34->30"                                        +"\n"+
	                        "  30-35->5"                                        +"\n"+
	                        "  5-F_36->31"                                        +"\n"+
	                        "  31-37->32"                                        +"\n"+
	                    "}"
	                    ,
	                    },
	    /////////////////  18   ///////////////////	
	                    {
	                    "#include<stdio.h>"                                                    +"\n"+
	                    "main()"                                                               +"\n"+
	                    "{"                                                                    +"\n"+
	                    " int grade;"                                                          +"\n"+
	                    " int a=0,b=0,counter = 1,c=1;"                                        +"\n"+
	                    " int i;"                                                              +"\n"+
	                    ""                                                                     +"\n"+
	                    "   while((grade=getchar())!=EOF)"                                     +"\n"+
	                    "    {"                                                                +"\n"+
	                    "      switch(grade)"                                                  +"\n"+
	                    "       {"                                                             +"\n"+
	                    "        case 'A': "                                                   +"\n"+
	                    "             for(i=0;i<=5;i++)"                                       +"\n"+
	                    "              {"                                                      +"\n"+
	                    "               switch(c)"                                             +"\n"+
	                    "                {"                                                    +"\n"+
	                    "                  case 1:c++;break;"                                  +"\n"+
	                    "                  case 2:printf(\"c\");break;"                          +"\n"+
	                    "                  default:printf(\"correct\");break;"                   +"\n"+
	                    "                }"                                                    +"\n"+
	                    "               printf(\"for\"); "                                       +"\n"+
	                    "              }  "                                                    +"\n"+
	                    "            break;"                                                   +"\n"+
	                    "        case 'B':"                                                    +"\n"+
	                    "             do{"                                                     +"\n"+
	                    "                printf(\"do\");"                                        +"\n"+
	                    "                  switch(c)"                                          +"\n"+
	                    "                    {"                                                +"\n"+
	                    "                     case 1:c++;break;"                               +"\n"+
	                    "                     case 2:printf(\"c\");break;"                       +"\n"+
	                    "                     default:printf(\"correct\");break;"                +"\n"+
	                    "                    }"                                                +"\n"+
	                    "                }"                                                    +"\n"+
	                    "             while(++counter<=10);"                                   +"\n"+
	                    "            break;"                                                   +"\n"+
	                    "        default:printf(\"incorrect!\");break;"                          +"\n"+
	                    "        }"                                                            +"\n"+
	                    "     } "                                                              +"\n"+
	                    "}"                                                                    
	                    ,
	                    "all"
	                    ,
	                    "//FunctionDefinition"
	                    ,
	                    "Graph {"                                                        +"\n"+
	                        "  0:func_head_main_0"                                        +"\n"+
	                        "  1:decl_stmt_1"                                        +"\n"+
	                        "  2:decl_stmt_2"                                        +"\n"+
	                        "  3:decl_stmt_3"                                        +"\n"+
	                        "  4:while_head_4"                                        +"\n"+
	                        "  5:switch_head_5"                                        +"\n"+
	                        "  6:label_head_case_6"                                        +"\n"+
	                        "  7:for_init_7"                                        +"\n"+
	                        "  8:for_head_8"                                        +"\n"+
	                        "  9:switch_head_9"                                        +"\n"+
	                        "  10:label_head_case_10"                                        +"\n"+
	                        "  11:stmt_11"                                        +"\n"+
	                        "  12:break_12"                                        +"\n"+
	                        "  13:label_head_case_13"                                        +"\n"+
	                        "  14:stmt_14"                                        +"\n"+
	                        "  15:break_15"                                        +"\n"+
	                        "  16:label_head_default_16"                                        +"\n"+
	                        "  17:stmt_17"                                        +"\n"+
	                        "  18:break_18"                                        +"\n"+
	                        "  19:switch_out_19"                                        +"\n"+
	                        "  20:stmt_20"                                        +"\n"+
	                        "  21:for_inc_21"                                        +"\n"+
	                        "  22:for_out_22"                                        +"\n"+
	                        "  23:break_23"                                        +"\n"+
	                        "  24:label_head_case_24"                                        +"\n"+
	                        "  25:do_while_head_25"                                        +"\n"+
	                        "  26:stmt_26"                                        +"\n"+
	                        "  27:switch_head_27"                                        +"\n"+
	                        "  28:label_head_case_28"                                        +"\n"+
	                        "  29:stmt_29"                                        +"\n"+
	                        "  30:break_30"                                        +"\n"+
	                        "  31:label_head_case_31"                                        +"\n"+
	                        "  32:stmt_32"                                        +"\n"+
	                        "  33:break_33"                                        +"\n"+
	                        "  34:label_head_default_34"                                        +"\n"+
	                        "  35:stmt_35"                                        +"\n"+
	                        "  36:break_36"                                        +"\n"+
	                        "  37:switch_out_37"                                        +"\n"+
	                        "  38:do_while_out1_38"                                        +"\n"+
	                        "  39:do_while_out2_39"                                        +"\n"+
	                        "  40:break_40"                                        +"\n"+
	                        "  41:label_head_default_41"                                        +"\n"+
	                        "  42:stmt_42"                                        +"\n"+
	                        "  43:break_43"                                        +"\n"+
	                        "  44:switch_out_44"                                        +"\n"+
	                        "  45:while_out_45"                                        +"\n"+
	                        "  46:func_out_main_46"                                        +"\n"+
	                        "  0-0->1"                                        +"\n"+
	                        "  1-1->2"                                        +"\n"+
	                        "  2-2->3"                                        +"\n"+
	                        "  3-3->4"                                        +"\n"+
	                        "  4-T_4->5"                                        +"\n"+
	                        "  5-5->6"                                        +"\n"+
	                        "  6-6->7"                                        +"\n"+
	                        "  7-7->8"                                        +"\n"+
	                        "  8-T_8->9"                                        +"\n"+
	                        "  9-9->10"                                        +"\n"+
	                        "  10-10->11"                                        +"\n"+
	                        "  11-11->12"                                        +"\n"+
	                        "  9-12->13"                                        +"\n"+
	                        "  13-13->14"                                        +"\n"+
	                        "  14-14->15"                                        +"\n"+
	                        "  9-15->16"                                        +"\n"+
	                        "  16-16->17"                                        +"\n"+
	                        "  17-17->18"                                        +"\n"+
	                        "  12-18->19"                                        +"\n"+
	                        "  15-19->19"                                        +"\n"+
	                        "  18-20->19"                                        +"\n"+
	                        "  19-21->20"                                        +"\n"+
	                        "  20-22->21"                                        +"\n"+
	                        "  21-23->8"                                        +"\n"+
	                        "  8-F_24->22"                                        +"\n"+
	                        "  22-25->23"                                        +"\n"+
	                        "  5-26->24"                                        +"\n"+
	                        "  24-27->25"                                        +"\n"+
	                        "  25-28->26"                                        +"\n"+
	                        "  26-29->27"                                        +"\n"+
	                        "  27-30->28"                                        +"\n"+
	                        "  28-31->29"                                        +"\n"+
	                        "  29-32->30"                                        +"\n"+
	                        "  27-33->31"                                        +"\n"+
	                        "  31-34->32"                                        +"\n"+
	                        "  32-35->33"                                        +"\n"+
	                        "  27-36->34"                                        +"\n"+
	                        "  34-37->35"                                        +"\n"+
	                        "  35-38->36"                                        +"\n"+
	                        "  30-39->37"                                        +"\n"+
	                        "  33-40->37"                                        +"\n"+
	                        "  36-41->37"                                        +"\n"+
	                        "  37-42->38"                                        +"\n"+
	                        "  38-T_43->25"                                        +"\n"+
	                        "  38-F_44->39"                                        +"\n"+
	                        "  39-45->40"                                        +"\n"+
	                        "  5-46->41"                                        +"\n"+
	                        "  41-47->42"                                        +"\n"+
	                        "  42-48->43"                                        +"\n"+
	                        "  23-49->44"                                        +"\n"+
	                        "  40-50->44"                                        +"\n"+
	                        "  43-51->44"                                        +"\n"+
	                        "  44-52->4"                                        +"\n"+
	                        "  4-F_53->45"                                        +"\n"+
	                        "  45-54->46"                                        +"\n"+
	                    "}"
	                    ,
	                    },
	    /////////////////  19   ///////////////////	
	                    {
	                    "#include<stdio.h>"                                                    +"\n"+
	                    "main()"                                                               +"\n"+
	                    "{"                                                                    +"\n"+
	                    " int grade;"                                                          +"\n"+
	                    " int a=0,b=0,counter = 1;"                                            +"\n"+
	                    " int i;"                                                              +"\n"+
	                    " for(i=0;i<=5;i++) "                                                  +"\n"+
	                    " {"                                                                   +"\n"+
	                    "   do{"                                                               +"\n"+
	                    "   printf(\"do\");"                                                     +"\n"+
	                    "   while((grade=getchar())!=EOF)"                                     +"\n"+
	                    "    {"                                                                +"\n"+
	                    "      switch(grade)"                                                  +"\n"+
	                    "       {"                                                             +"\n"+
	                    "        case 'A':++a;break;"                                          +"\n"+
	                    "        case 'B':++b;break;"                                          +"\n"+
	                    "        default:printf(\"incorrect!\");break;"                          +"\n"+
	                    "        }"                                                            +"\n"+
	                    "		if(grade>0)"                                                        +"\n"+
	                    "			return;"                                                           +"\n"+
	                    "     } "                                                              +"\n"+
	                    "	if(i==3)"                                                            +"\n"+
	                    "		return;"                                                            +"\n"+
	                    "    }"                                                                +"\n"+
	                    "   while(++counter<=10);"                                             +"\n"+
	                    "   return 0;"                                                         +"\n"+
	                    "  }"                                                                  +"\n"+
	                    "}"                                                                    
	                    ,
	                    "all"
	                    ,
	                    "//FunctionDefinition"
	                    ,
	                    "Graph {"                                                        +"\n"+
	                        "  0:func_head_main_0"                                        +"\n"+
	                        "  1:decl_stmt_1"                                        +"\n"+
	                        "  2:decl_stmt_2"                                        +"\n"+
	                        "  3:decl_stmt_3"                                        +"\n"+
	                        "  4:for_init_4"                                        +"\n"+
	                        "  5:for_head_5"                                        +"\n"+
	                        "  6:do_while_head_6"                                        +"\n"+
	                        "  7:stmt_7"                                        +"\n"+
	                        "  8:while_head_8"                                        +"\n"+
	                        "  9:switch_head_9"                                        +"\n"+
	                        "  10:label_head_case_10"                                        +"\n"+
	                        "  11:stmt_11"                                        +"\n"+
	                        "  12:break_12"                                        +"\n"+
	                        "  13:label_head_case_13"                                        +"\n"+
	                        "  14:stmt_14"                                        +"\n"+
	                        "  15:break_15"                                        +"\n"+
	                        "  16:label_head_default_16"                                        +"\n"+
	                        "  17:stmt_17"                                        +"\n"+
	                        "  18:break_18"                                        +"\n"+
	                        "  19:switch_out_19"                                        +"\n"+
	                        "  20:if_head_20"                                        +"\n"+
	                        "  21:return_21"                                        +"\n"+
	                        "  22:if_out_22"                                        +"\n"+
	                        "  23:while_out_23"                                        +"\n"+
	                        "  24:if_head_24"                                        +"\n"+
	                        "  25:return_25"                                        +"\n"+
	                        "  26:if_out_26"                                        +"\n"+
	                        "  27:do_while_out1_27"                                        +"\n"+
	                        "  28:do_while_out2_28"                                        +"\n"+
	                        "  29:return_29"                                        +"\n"+
	                        "  30:for_inc_30"                                        +"\n"+
	                        "  31:for_out_31"                                        +"\n"+
	                        "  32:func_out_main_32"                                        +"\n"+
	                        "  0-0->1"                                        +"\n"+
	                        "  1-1->2"                                        +"\n"+
	                        "  2-2->3"                                        +"\n"+
	                        "  3-3->4"                                        +"\n"+
	                        "  4-4->5"                                        +"\n"+
	                        "  5-T_5->6"                                        +"\n"+
	                        "  6-6->7"                                        +"\n"+
	                        "  7-7->8"                                        +"\n"+
	                        "  8-T_8->9"                                        +"\n"+
	                        "  9-9->10"                                        +"\n"+
	                        "  10-10->11"                                        +"\n"+
	                        "  11-11->12"                                        +"\n"+
	                        "  9-12->13"                                        +"\n"+
	                        "  13-13->14"                                        +"\n"+
	                        "  14-14->15"                                        +"\n"+
	                        "  9-15->16"                                        +"\n"+
	                        "  16-16->17"                                        +"\n"+
	                        "  17-17->18"                                        +"\n"+
	                        "  12-18->19"                                        +"\n"+
	                        "  15-19->19"                                        +"\n"+
	                        "  18-20->19"                                        +"\n"+
	                        "  19-21->20"                                        +"\n"+
	                        "  20-T_22->21"                                        +"\n"+
	                        "  20-F_23->22"                                        +"\n"+
	                        "  22-24->8"                                        +"\n"+
	                        "  8-F_25->23"                                        +"\n"+
	                        "  23-26->24"                                        +"\n"+
	                        "  24-T_27->25"                                        +"\n"+
	                        "  24-F_28->26"                                        +"\n"+
	                        "  26-29->27"                                        +"\n"+
	                        "  27-T_30->6"                                        +"\n"+
	                        "  27-F_31->28"                                        +"\n"+
	                        "  28-32->29"                                        +"\n"+
	                        "  30-33->5"                                        +"\n"+
	                        "  5-F_34->31"                                        +"\n"+
	                        "  31-35->32"                                        +"\n"+
	                        "  21-36->32"                                        +"\n"+
	                        "  25-37->32"                                        +"\n"+
	                        "  29-38->32"                                        +"\n"+
	                    "}"
	                    ,
	                    },
	    /////////////////  20   ///////////////////	
	                    {
	                    "f(){"                                                                 +"\n"+
	                    "int ff(){"                                                            +"\n"+
	                    " int i;"                                                              +"\n"+
	                    " if(i>0)"                                                             +"\n"+
	                    "	return i;"                                                           +"\n"+
	                    "}"                                                                    +"\n"+
	                    "int j;"                                                               +"\n"+
	                    "ff();"                                                                +"\n"+
	                    "return j;"                                                            +"\n"+
	                    "}"                                                                    
	                    ,
	                    "gcc"
	                    ,
	                    "//FunctionDefinition"
	                    ,
	                    "Graph {"                                                        +"\n"+
	                        "  0:func_head_f_0"                                        +"\n"+
	                        "  1:decl_stmt_1"                                        +"\n"+
	                        "  2:stmt_2"                                        +"\n"+
	                        "  3:return_3"                                        +"\n"+
	                        "  4:func_out_f_4"                                        +"\n"+
	                        "  0-0->1"                                        +"\n"+
	                        "  1-1->2"                                        +"\n"+
	                        "  2-2->3"                                        +"\n"+
	                        "  3-3->4"                                        +"\n"+
	                    "}"
	                    ,
	                    },

	             	   ////////////////		/  21   ///////////////////	
		  	              {
		  	              "float add(float x,float y)"                                           +"\n"+
		  	              "{"                                                                    +"\n"+
		  	              "float z;"                                                             +"\n"+
		  	              "z=x+y;"                                                               +"\n"+
		  	              "return(z);"                                                           +"\n"+
		  	              "}"                                                                    
		  	              ,
		  	              "all"
		  	              ,
		  	              "//FunctionDefinition"
		  	              ,
		  	              "Graph {"                                                        +"\n"+
		  	                  "  0:func_head_add_0"                                        +"\n"+
		  	                  "  1:decl_stmt_1"                                        +"\n"+
		  	                  "  2:stmt_2"                                        +"\n"+
		  	                  "  3:return_3"                                        +"\n"+
		  	                  "  4:func_out_add_4"                                        +"\n"+
		  	                  "  0-0->1"                                        +"\n"+
		  	                  "  1-1->2"                                        +"\n"+
		  	                  "  2-2->3"                                        +"\n"+
		  	                  "  3-3->4"                                        +"\n"+
		  	              "}"
		  	              ,
		  	              },
////////////////		  	/  22   ///////////////////	
		  	              {
		  	              "void main() {"                                                        +"\n"+
		  	              "int count=0;"                                                         +"\n"+
		  	              "label1: "                                                             +"\n"+
		  	              "do{"                                                                  +"\n"+
		  	              "    count=count+1;"                                                   +"\n"+
		  	              "    if(count==10)"                                                    +"\n"+
		  	              "        break;"                                                       +"\n"+
		  	              "    if(count==20)"                                                    +"\n"+
		  	              "       goto label2;"                                                  +"\n"+
		  	              "}while(count<30);"                                                    +"\n"+
		  	              "goto label1;"                                                         +"\n"+
		  	              "label2:count=100;"                                                    +"\n"+
		  	              "}"                                                                    
		  	              ,
		  	              "all"
		  	              ,
		  	              "//FunctionDefinition"
		  	              ,
		  	              "Graph {"                                                        +"\n"+
		  	                  "  0:func_head_main_0"                                        +"\n"+
		  	                  "  1:decl_stmt_1"                                        +"\n"+
		  	                  "  2:label_head_label1_2"                                        +"\n"+
		  	                  "  3:do_while_head_3"                                        +"\n"+
		  	                  "  4:stmt_4"                                        +"\n"+
		  	                  "  5:if_head_5"                                        +"\n"+
		  	                  "  6:break_6"                                        +"\n"+
		  	                  "  7:if_out_7"                                        +"\n"+
		  	                  "  8:if_head_8"                                        +"\n"+
		  	                  "  9:goto_9"                                        +"\n"+
		  	                  "  10:if_out_10"                                        +"\n"+
		  	                  "  11:do_while_out1_11"                                        +"\n"+
		  	                  "  12:do_while_out2_12"                                        +"\n"+
		  	                  "  13:goto_13"                                        +"\n"+
		  	                  "  14:label_head_label2_14"                                        +"\n"+
		  	                  "  15:stmt_15"                                        +"\n"+
		  	                  "  16:func_out_main_16"                                        +"\n"+
		  	                  "  0-0->1"                                        +"\n"+
		  	                  "  1-1->2"                                        +"\n"+
		  	                  "  2-2->3"                                        +"\n"+
		  	                  "  3-3->4"                                        +"\n"+
		  	                  "  4-4->5"                                        +"\n"+
		  	                  "  5-T_5->6"                                        +"\n"+
		  	                  "  5-F_6->7"                                        +"\n"+
		  	                  "  7-7->8"                                        +"\n"+
		  	                  "  8-T_8->9"                                        +"\n"+
		  	                  "  8-F_9->10"                                        +"\n"+
		  	                  "  10-10->11"                                        +"\n"+
		  	                  "  11-T_11->3"                                        +"\n"+
		  	                  "  11-F_12->12"                                        +"\n"+
		  	                  "  6-13->12"                                        +"\n"+
		  	                  "  12-14->13"                                        +"\n"+
		  	                  "  14-15->15"                                        +"\n"+
		  	                  "  15-16->16"                                        +"\n"+
		  	                  "  9-17->14"                                        +"\n"+
		  	                  "  13-18->2"                                        +"\n"+
		  	              "}"
		  	              ,
		  	              },

////////////////		  	/  23   ///////////////////	
		  	            {
		  	            "void main() {"                                                        +"\n"+
		  	            " int i=10;"                                                           +"\n"+
		  	            " label1: do{"                                                         +"\n"+
		  	            "   if(i>10)"                                                          +"\n"+
		  	            "     continue;"                                                       +"\n"+
		  	            "   else "                                                             +"\n"+
		  	            "     if(i<10)"                                                        +"\n"+
		  	            "       break;"                                                        +"\n"+
		  	            "     else"                                                            +"\n"+
		  	            "       i++;"                                                          +"\n"+
		  	            "		 }"                                                                 +"\n"+
		  	            "  while(i<=20);"                                                      +"\n"+
		  	            "}"                                                                    
		  	            ,
		  	            "all"
		  	            ,
		  	            "//FunctionDefinition"
		  	            ,
		  	            "Graph {"                                                        +"\n"+
		  	                "  0:func_head_main_0"                                        +"\n"+
		  	                "  1:decl_stmt_1"                                        +"\n"+
		  	                "  2:label_head_label1_2"                                        +"\n"+
		  	                "  3:do_while_head_3"                                        +"\n"+
		  	                "  4:if_head_4"                                        +"\n"+
		  	                "  5:continue_5"                                        +"\n"+
		  	                "  6:if_head_6"                                        +"\n"+
		  	                "  7:break_7"                                        +"\n"+
		  	                "  8:stmt_8"                                        +"\n"+
		  	                "  9:if_out_9"                                        +"\n"+
		  	                "  10:if_out_10"                                        +"\n"+
		  	                "  11:do_while_out1_11"                                        +"\n"+
		  	                "  12:do_while_out2_12"                                        +"\n"+
		  	                "  13:func_out_main_13"                                        +"\n"+
		  	                "  0-0->1"                                        +"\n"+
		  	                "  1-1->2"                                        +"\n"+
		  	                "  2-2->3"                                        +"\n"+
		  	                "  3-3->4"                                        +"\n"+
		  	                "  4-T_4->5"                                        +"\n"+
		  	                "  4-F_5->6"                                        +"\n"+
		  	                "  6-T_6->7"                                        +"\n"+
		  	                "  6-F_7->8"                                        +"\n"+
		  	                "  8-8->9"                                        +"\n"+
		  	                "  9-9->10"                                        +"\n"+
		  	                "  10-10->11"                                        +"\n"+
		  	                "  11-T_11->3"                                        +"\n"+
		  	                "  11-F_12->12"                                        +"\n"+
		  	                "  7-13->12"                                        +"\n"+
		  	                "  5-14->11"                                        +"\n"+
		  	                "  12-15->13"                                        +"\n"+
		  	            "}"
		  	            ,
		  	            },
////////////////		  	/  24   ///////////////////	
		  	              {
		  	              "float add(float x,float y)"                                           +"\n"+
		  	              "{"                                                                    +"\n"+
		  	              "float z;"                                                             +"\n"+
		  	              "z=x+y;"                                                               +"\n"+
		  	              "return(z);"                                                           +"\n"+
		  	              "}"                                                                    +"\n"+
		  	              "main() {"                                                             +"\n"+
		  	              "int count = 1;"                                                       +"\n"+
		  	              "float count2;"                                                        +"\n"+
		  	              "int count3=0;"                                                        +"\n"+
		  	              "label1: "                                                             +"\n"+
		  	              "do{"                                                                  +"\n"+
		  	              "    count=count+1;"                                                   +"\n"+
		  	              "    if(count==10)"                                                    +"\n"+
		  	              "        break;"                                                       +"\n"+
		  	              "    if(count==20)"                                                    +"\n"+
		  	              "       goto label2;"                                                  +"\n"+
		  	              "}while(count<30);"                                                    +"\n"+
		  	              "goto label1;"                                                         +"\n"+
		  	              "label2:count2=add(1.0+2.0);"                                          +"\n"+
		  	              "do{"                                                                  +"\n"+
		  	              "   count3=count3+1;"                                                  +"\n"+
		  	              "   if(count3==4){"                                                    +"\n"+
		  	              "      count2=count2+1.0;"                                             +"\n"+
		  	              "      continue;"                                                      +"\n"+
		  	              "    } "                                                               +"\n"+
		  	              "  else if(count3==7)"                                                 +"\n"+
		  	              "   break;"                                                            +"\n"+
		  	              "}while(count3<10);"                                                   +"\n"+
		  	              "}"                                                                    
		  	              ,
		  	              "all"
		  	              ,
		  	              "//FunctionDefinition[@Type='add(float,float)float']"
		  	              ,
		  	              "Graph {"                                                        +"\n"+
		  	                  "  0:func_head_add_0"                                        +"\n"+
		  	                  "  1:decl_stmt_1"                                        +"\n"+
		  	                  "  2:stmt_2"                                        +"\n"+
		  	                  "  3:return_3"                                        +"\n"+
		  	                  "  4:func_out_add_4"                                        +"\n"+
		  	                  "  0-0->1"                                        +"\n"+
		  	                  "  1-1->2"                                        +"\n"+
		  	                  "  2-2->3"                                        +"\n"+
		  	                  "  3-3->4"                                        +"\n"+
		  	              "}"
		  	              ,
		  	              },

////////////////		  	/  25   ///////////////////	
		  	            {
		  	            "float add(float x,float y)"                                           +"\n"+
		  	            "{"                                                                    +"\n"+
		  	            "float z;"                                                             +"\n"+
		  	            "z=x+y;"                                                               +"\n"+
		  	            "return(z);"                                                           +"\n"+
		  	            "}"                                                                    +"\n"+
		  	            "main() {"                                                             +"\n"+
		  	            "int count = 1;"                                                       +"\n"+
		  	            "float count2;"                                                        +"\n"+
		  	            "int count3=0;"                                                        +"\n"+
		  	            "label1: "                                                             +"\n"+
		  	            "do{"                                                                  +"\n"+
		  	            "    count=count+1;"                                                   +"\n"+
		  	            "    if(count==10)"                                                    +"\n"+
		  	            "        break;"                                                       +"\n"+
		  	            "    if(count==20)"                                                    +"\n"+
		  	            "       goto label2;"                                                  +"\n"+
		  	            "}while(count<30);"                                                    +"\n"+
		  	            "goto label1;"                                                         +"\n"+
		  	            "label2:count2=add(1.0+2.0);"                                          +"\n"+
		  	            "do{"                                                                  +"\n"+
		  	            "   count3=count3+1;"                                                  +"\n"+
		  	            "   if(count3==4){"                                                    +"\n"+
		  	            "      count2=count2+1.0;"                                             +"\n"+
		  	            "      continue;"                                                      +"\n"+
		  	            "    } "                                                               +"\n"+
		  	            "  else if(count3==7)"                                                 +"\n"+
		  	            "   break;"                                                            +"\n"+
		  	            "}while(count3<10);"                                                   +"\n"+
		  	            "}"                                                                    
		  	            ,
		  	            "all"
		  	            ,
		  	            "//FunctionDefinition[@Type='main()int']"
		  	            ,
		  	            "Graph {"                                                        +"\n"+
		  	                "  0:func_head_main_0"                                        +"\n"+
		  	                "  1:decl_stmt_1"                                        +"\n"+
		  	                "  2:decl_stmt_2"                                        +"\n"+
		  	                "  3:decl_stmt_3"                                        +"\n"+
		  	                "  4:label_head_label1_4"                                        +"\n"+
		  	                "  5:do_while_head_5"                                        +"\n"+
		  	                "  6:stmt_6"                                        +"\n"+
		  	                "  7:if_head_7"                                        +"\n"+
		  	                "  8:break_8"                                        +"\n"+
		  	                "  9:if_out_9"                                        +"\n"+
		  	                "  10:if_head_10"                                        +"\n"+
		  	                "  11:goto_11"                                        +"\n"+
		  	                "  12:if_out_12"                                        +"\n"+
		  	                "  13:do_while_out1_13"                                        +"\n"+
		  	                "  14:do_while_out2_14"                                        +"\n"+
		  	                "  15:goto_15"                                        +"\n"+
		  	                "  16:label_head_label2_16"                                        +"\n"+
		  	                "  17:stmt_17"                                        +"\n"+
		  	                "  18:do_while_head_18"                                        +"\n"+
		  	                "  19:stmt_19"                                        +"\n"+
		  	                "  20:if_head_20"                                        +"\n"+
		  	                "  21:stmt_21"                                        +"\n"+
		  	                "  22:continue_22"                                        +"\n"+
		  	                "  23:if_head_23"                                        +"\n"+
		  	                "  24:break_24"                                        +"\n"+
		  	                "  25:if_out_25"                                        +"\n"+
		  	                "  26:if_out_26"                                        +"\n"+
		  	                "  27:do_while_out1_27"                                        +"\n"+
		  	                "  28:do_while_out2_28"                                        +"\n"+
		  	                "  29:func_out_main_29"                                        +"\n"+
		  	                "  0-0->1"                                        +"\n"+
		  	                "  1-1->2"                                        +"\n"+
		  	                "  2-2->3"                                        +"\n"+
		  	                "  3-3->4"                                        +"\n"+
		  	                "  4-4->5"                                        +"\n"+
		  	                "  5-5->6"                                        +"\n"+
		  	                "  6-6->7"                                        +"\n"+
		  	                "  7-T_7->8"                                        +"\n"+
		  	                "  7-F_8->9"                                        +"\n"+
		  	                "  9-9->10"                                        +"\n"+
		  	                "  10-T_10->11"                                        +"\n"+
		  	                "  10-F_11->12"                                        +"\n"+
		  	                "  12-12->13"                                        +"\n"+
		  	                "  13-T_13->5"                                        +"\n"+
		  	                "  13-F_14->14"                                        +"\n"+
		  	                "  8-15->14"                                        +"\n"+
		  	                "  14-16->15"                                        +"\n"+
		  	                "  16-17->17"                                        +"\n"+
		  	                "  17-18->18"                                        +"\n"+
		  	                "  18-19->19"                                        +"\n"+
		  	                "  19-20->20"                                        +"\n"+
		  	                "  20-T_21->21"                                        +"\n"+
		  	                "  21-22->22"                                        +"\n"+
		  	                "  20-F_23->23"                                        +"\n"+
		  	                "  23-T_24->24"                                        +"\n"+
		  	                "  23-F_25->25"                                        +"\n"+
		  	                "  25-26->26"                                        +"\n"+
		  	                "  26-27->27"                                        +"\n"+
		  	                "  27-T_28->18"                                        +"\n"+
		  	                "  27-F_29->28"                                        +"\n"+
		  	                "  24-30->28"                                        +"\n"+
		  	                "  22-31->27"                                        +"\n"+
		  	                "  28-32->29"                                        +"\n"+
		  	                "  11-33->16"                                        +"\n"+
		  	                "  15-34->4"                                        +"\n"+
		  	            "}"
		  	            ,
		  	            },
////////////////		  	26   ///////////////////	
		  	            {
		  	            "void main()"                                                          +"\n"+
		  	            "{"                                                                    +"\n"+
		  	            "  int i,j,sum=0;"                                                     +"\n"+
		  	            "  i=1;"                                                               +"\n"+
		  	            "label1:"                                                              +"\n"+
		  	            "  do{"                                                                +"\n"+
		  	            "     sum=sum+i;"                                                      +"\n"+
		  	            "     i++;"                                                            +"\n"+
		  	            "        do{"                                                          +"\n"+
		  	            "            if(i==10)"                                                +"\n"+
		  	            "               continue;"                                             +"\n"+
		  	            "            else break;"                                              +"\n"+
		  	            "           }"                                                         +"\n"+
		  	            "        while(i<=20);"                                                +"\n"+
		  	            "     if(i==50)"                                                       +"\n"+
		  	            "       break;"                                                        +"\n"+
		  	            "    }"                                                                +"\n"+
		  	            "   while(i<=100);"                                                    +"\n"+
		  	            "i++;"                                                                 +"\n"+
		  	            "if(i>=00)"                                                            +"\n"+
		  	            "  goto label2;"                                                       +"\n"+
		  	            "goto label1;"                                                         +"\n"+
		  	            "  label2: (i>100)?(j=0):(j=1);"                                       +"\n"+
		  	            "    if(j==0)"                                                         +"\n"+
		  	            "      printf(\"%d\",sum);"                                              +"\n"+
		  	            "    else"                                                             +"\n"+
		  	            "      printf(\"%d\",i);   "                                             +"\n"+
		  	            "}"                                                                    
		  	            ,
		  	            "all"
		  	            ,
		  	            "//FunctionDefinition"
		  	            ,
		  	            "Graph {"                                                        +"\n"+
		  	                "  0:func_head_main_0"                                        +"\n"+
		  	                "  1:decl_stmt_1"                                        +"\n"+
		  	                "  2:stmt_2"                                        +"\n"+
		  	                "  3:label_head_label1_3"                                        +"\n"+
		  	                "  4:do_while_head_4"                                        +"\n"+
		  	                "  5:stmt_5"                                        +"\n"+
		  	                "  6:stmt_6"                                        +"\n"+
		  	                "  7:do_while_head_7"                                        +"\n"+
		  	                "  8:if_head_8"                                        +"\n"+
		  	                "  9:continue_9"                                        +"\n"+
		  	                "  10:break_10"                                        +"\n"+
		  	                "  11:do_while_out1_11"                                        +"\n"+
		  	                "  12:do_while_out2_12"                                        +"\n"+
		  	                "  13:if_head_13"                                        +"\n"+
		  	                "  14:break_14"                                        +"\n"+
		  	                "  15:if_out_15"                                        +"\n"+
		  	                "  16:do_while_out1_16"                                        +"\n"+
		  	                "  17:do_while_out2_17"                                        +"\n"+
		  	                "  18:stmt_18"                                        +"\n"+
		  	                "  19:if_head_19"                                        +"\n"+
		  	                "  20:goto_20"                                        +"\n"+
		  	                "  21:if_out_21"                                        +"\n"+
		  	                "  22:goto_22"                                        +"\n"+
		  	                "  23:label_head_label2_23"                                        +"\n"+
		  	                "  24:stmt_24"                                        +"\n"+
		  	                "  25:if_head_25"                                        +"\n"+
		  	                "  26:stmt_26"                                        +"\n"+
		  	                "  27:stmt_27"                                        +"\n"+
		  	                "  28:if_out_28"                                        +"\n"+
		  	                "  29:func_out_main_29"                                        +"\n"+
		  	                "  0-0->1"                                        +"\n"+
		  	                "  1-1->2"                                        +"\n"+
		  	                "  2-2->3"                                        +"\n"+
		  	                "  3-3->4"                                        +"\n"+
		  	                "  4-4->5"                                        +"\n"+
		  	                "  5-5->6"                                        +"\n"+
		  	                "  6-6->7"                                        +"\n"+
		  	                "  7-7->8"                                        +"\n"+
		  	                "  8-T_8->9"                                        +"\n"+
		  	                "  8-F_9->10"                                        +"\n"+
		  	                "  11-T_10->7"                                        +"\n"+
		  	                "  11-F_11->12"                                        +"\n"+
		  	                "  10-12->12"                                        +"\n"+
		  	                "  9-13->11"                                        +"\n"+
		  	                "  12-14->13"                                        +"\n"+
		  	                "  13-T_15->14"                                        +"\n"+
		  	                "  13-F_16->15"                                        +"\n"+
		  	                "  15-17->16"                                        +"\n"+
		  	                "  16-T_18->4"                                        +"\n"+
		  	                "  16-F_19->17"                                        +"\n"+
		  	                "  14-20->17"                                        +"\n"+
		  	                "  17-21->18"                                        +"\n"+
		  	                "  18-22->19"                                        +"\n"+
		  	                "  19-T_23->20"                                        +"\n"+
		  	                "  19-F_24->21"                                        +"\n"+
		  	                "  21-25->22"                                        +"\n"+
		  	                "  23-26->24"                                        +"\n"+
		  	                "  24-27->25"                                        +"\n"+
		  	                "  25-T_28->26"                                        +"\n"+
		  	                "  25-F_29->27"                                        +"\n"+
		  	                "  26-30->28"                                        +"\n"+
		  	                "  27-31->28"                                        +"\n"+
		  	                "  28-32->29"                                        +"\n"+
		  	                "  20-33->23"                                        +"\n"+
		  	                "  22-34->3"                                        +"\n"+
		  	            "}"
		  	            ,
		  	            },
		  	            /////////////////  27   ///////////////////	
		                    {
		                    "#include <stdio.h>"                                                   +"\n"+
		                    " main(){"                                                             +"\n"+
		                    "  int a=1;"                                                           +"\n"+
		                    "  int b=2;"                                                           +"\n"+
		                    "  switch(a){"                                                         +"\n"+
		                    "  case 1 : a++;break;"                                                +"\n"+
		                    "  case 2 : return b;break;"                                           +"\n"+
		                    "  default: return a;break;"                                           +"\n"+
		                    "  }"                                                                  +"\n"+
		                    "}"                                                                    
		                    ,
		                    "all"
		                    ,
		                    "//FunctionDefinition"
		                    ,
		                    "Graph {"                                                        +"\n"+
		                        "  0:func_head_main_0"                                        +"\n"+
		                        "  1:decl_stmt_1"                                        +"\n"+
		                        "  2:decl_stmt_2"                                        +"\n"+
		                        "  3:switch_head_3"                                        +"\n"+
		                        "  4:label_head_case_4"                                        +"\n"+
		                        "  5:stmt_5"                                        +"\n"+
		                        "  6:break_6"                                        +"\n"+
		                        "  7:label_head_case_7"                                        +"\n"+
		                        "  8:return_8"                                        +"\n"+
		                        "  9:break_9"                                        +"\n"+
		                        "  10:label_head_default_10"                                        +"\n"+
		                        "  11:return_11"                                        +"\n"+
		                        "  12:break_12"                                        +"\n"+
		                        "  13:switch_out_13"                                        +"\n"+
		                        "  14:func_out_main_14"                                        +"\n"+
		                        "  0-0->1"                                        +"\n"+
		                        "  1-1->2"                                        +"\n"+
		                        "  2-2->3"                                        +"\n"+
		                        "  3-3->4"                                        +"\n"+
		                        "  4-4->5"                                        +"\n"+
		                        "  5-5->6"                                        +"\n"+
		                        "  3-6->7"                                        +"\n"+
		                        "  7-7->8"                                        +"\n"+
		                        "  3-8->10"                                        +"\n"+
		                        "  10-9->11"                                        +"\n"+
		                        "  6-10->13"                                        +"\n"+
		                        "  9-11->13"                                        +"\n"+
		                        "  12-12->13"                                        +"\n"+
		                        "  13-13->14"                                        +"\n"+
		                        "  8-14->14"                                        +"\n"+
		                        "  11-15->14"                                        +"\n"+
		                    "}"
		                    ,
		                    },
		    /////////////////  28   ///////////////////	
		                    {
		                    "int i;"                                                               +"\n"+
		                    "f(){"                                                                 +"\n"+
		                    " int ff(int i){"                                                      +"\n"+
		                    "	i=1;"                                                                +"\n"+
		                    "	while(i>1)"                                                          +"\n"+
		                    "	{"                                                                   +"\n"+
		                    "	  i--;"                                                              +"\n"+
		                    "	  if(i>1)	goto label;"                                               +"\n"+
		                    "	  else break;"                                                       +"\n"+
		                    "	}"                                                                   +"\n"+
		                    "	label:"                                                              +"\n"+
		                    "	  i=100;"                                                            +"\n"+
		                    " }"                                                                   +"\n"+
		                    " int j=1;"                                                            +"\n"+
		                    " if(j>0)"                                                             +"\n"+
		                    "	return j;"                                                           +"\n"+
		                    "}"                                                                    
		                    ,
		                    "gcc"
		                    ,
		                    "//NestedFunctionDefinition"
		                    ,
		                    "Graph {"                                                        +"\n"+
		                        "  0:nestedfunc_head_ff_0"                                        +"\n"+
		                        "  1:stmt_1"                                        +"\n"+
		                        "  2:while_head_2"                                        +"\n"+
		                        "  3:stmt_3"                                        +"\n"+
		                        "  4:if_head_4"                                        +"\n"+
		                        "  5:goto_5"                                        +"\n"+
		                        "  6:break_6"                                        +"\n"+
		                        "  7:while_out_7"                                        +"\n"+
		                        "  8:label_head_label_8"                                        +"\n"+
		                        "  9:stmt_9"                                        +"\n"+
		                        "  10:nestedfunc_out_ff_10"                                        +"\n"+
		                        "  0-0->1"                                        +"\n"+
		                        "  1-1->2"                                        +"\n"+
		                        "  2-T_2->3"                                        +"\n"+
		                        "  3-3->4"                                        +"\n"+
		                        "  4-T_4->5"                                        +"\n"+
		                        "  4-F_5->6"                                        +"\n"+
		                        "  2-F_6->7"                                        +"\n"+
		                        "  6-7->7"                                        +"\n"+
		                        "  7-8->8"                                        +"\n"+
		                        "  8-9->9"                                        +"\n"+
		                        "  9-10->10"                                        +"\n"+
		                        "  5-11->8"                                        +"\n"+
		                    "}"
		                    ,
		                    },
		    /////////////////  29   ///////////////////	
		                    {
		                    "f(){"                                                                 +"\n"+
		                    "int i=3;"                                                             +"\n"+
		                    "switch(i){"                                                           +"\n"+
		                    "case 1:i++;"                                                          +"\n"+
		                    "case 2:i++;"                                                          +"\n"+
		                    "default:i++;"                                                         +"\n"+
		                    "}"                                                                    +"\n"+
		                    ""                                                                     +"\n"+
		                    "for(;i<10;)"                                                          +"\n"+
		                    "{"                                                                    +"\n"+
		                    "	int j=i++;continue;"                                                 +"\n"+
		                    "}"                                                                    +"\n"+
		                    "while(i<50)"                                                          +"\n"+
		                    "{"                                                                    +"\n"+
		                    "	i++;continue;"                                                       +"\n"+
		                    "}"                                                                    +"\n"+
		                    "goto l;"                                                              +"\n"+
		                    "if(i>100);"                                                           +"\n"+
		                    "l:"                                                                   +"\n"+
		                    "	i++;"                                                                +"\n"+
		                    "}"                                                                    
		                    ,
		                    "all"
		                    ,
		                    "//FunctionDefinition"
		                    ,
		                    "Graph {"                                                        +"\n"+
		                        "  0:func_head_f_0"                                        +"\n"+
		                        "  1:decl_stmt_1"                                        +"\n"+
		                        "  2:switch_head_2"                                        +"\n"+
		                        "  3:label_head_case_3"                                        +"\n"+
		                        "  4:stmt_4"                                        +"\n"+
		                        "  5:label_head_case_5"                                        +"\n"+
		                        "  6:stmt_6"                                        +"\n"+
		                        "  7:label_head_default_7"                                        +"\n"+
		                        "  8:stmt_8"                                        +"\n"+
		                        "  9:switch_out_9"                                        +"\n"+
		                        "  10:for_head_10"                                        +"\n"+
		                        "  11:decl_stmt_11"                                        +"\n"+
		                        "  12:continue_12"                                        +"\n"+
		                        "  13:for_out_13"                                        +"\n"+
		                        "  14:while_head_14"                                        +"\n"+
		                        "  15:stmt_15"                                        +"\n"+
		                        "  16:continue_16"                                        +"\n"+
		                        "  17:while_out_17"                                        +"\n"+
		                        "  18:goto_18"                                        +"\n"+
		                        "  19:if_head_19"                                        +"\n"+
		                        "  20:stmt_20"                                        +"\n"+
		                        "  21:if_out_21"                                        +"\n"+
		                        "  22:label_head_l_22"                                        +"\n"+
		                        "  23:stmt_23"                                        +"\n"+
		                        "  24:func_out_f_24"                                        +"\n"+
		                        "  0-0->1"                                        +"\n"+
		                        "  1-1->2"                                        +"\n"+
		                        "  2-2->3"                                        +"\n"+
		                        "  3-3->4"                                        +"\n"+
		                        "  4-4->5"                                        +"\n"+
		                        "  2-5->5"                                        +"\n"+
		                        "  5-6->6"                                        +"\n"+
		                        "  6-7->7"                                        +"\n"+
		                        "  2-8->7"                                        +"\n"+
		                        "  7-9->8"                                        +"\n"+
		                        "  8-10->9"                                        +"\n"+
		                        "  9-11->10"                                        +"\n"+
		                        "  10-T_12->11"                                        +"\n"+
		                        "  11-13->12"                                        +"\n"+
		                        "  10-F_14->13"                                        +"\n"+
		                        "  12-15->10"                                        +"\n"+
		                        "  13-16->14"                                        +"\n"+
		                        "  14-T_17->15"                                        +"\n"+
		                        "  15-18->16"                                        +"\n"+
		                        "  14-F_19->17"                                        +"\n"+
		                        "  16-20->14"                                        +"\n"+
		                        "  17-21->18"                                        +"\n"+
		                        "  19-T_22->20"                                        +"\n"+
		                        "  20-23->21"                                        +"\n"+
		                        "  19-F_24->21"                                        +"\n"+
		                        "  21-25->22"                                        +"\n"+
		                        "  22-26->23"                                        +"\n"+
		                        "  23-27->24"                                        +"\n"+
		                        "  18-28->22"                                        +"\n"+
		                    "}"
		                    ,
		                    },
		    /////////////////  30   ///////////////////	
		                    {
		                    "f(){"                                                                 +"\n"+
		                    "if(i>1){"                                                             +"\n"+
		                    ""                                                                     +"\n"+
		                    "}"                                                                    +"\n"+
		                    "}"                                                                    
		                    ,
		                    "all"
		                    ,
		                    "//FunctionDefinition"
		                    ,
		                    "Graph {"                                                        +"\n"+
		                        "  0:func_head_f_0"                                        +"\n"+
		                        "  1:if_head_1"                                        +"\n"+
		                        "  2:if_out_2"                                        +"\n"+
		                        "  3:func_out_f_3"                                        +"\n"+
		                        "  0-0->1"                                        +"\n"+
		                        "  1-T_1->2"                                        +"\n"+
		                        "  1-F_2->2"                                        +"\n"+
		                        "  2-3->3"                                        +"\n"+
		                    "}"
		                    ,
		                    },
		    /////////////////  31   ///////////////////	
		                    {
		                    "f(){"                                                                 +"\n"+
		                    "int ff(){"                                                            +"\n"+
		                    " int i;"                                                              +"\n"+
		                    " if(i>0)"                                                             +"\n"+
		                    "	return i;"                                                           +"\n"+
		                    "}"                                                                    +"\n"+
		                    "int j;"                                                               +"\n"+
		                    "ff();"                                                                +"\n"+
		                    "return j;"                                                            +"\n"+
		                    "}"                                                                    
		                    ,
		                    "gcc"
		                    ,
		                    "//NestedFunctionDefinition"
		                    ,
		                    "Graph {"                                                        +"\n"+
		                        "  0:nestedfunc_head_ff_0"                                        +"\n"+
		                        "  1:decl_stmt_1"                                        +"\n"+
		                        "  2:if_head_2"                                        +"\n"+
		                        "  3:return_3"                                        +"\n"+
		                        "  4:if_out_4"                                        +"\n"+
		                        "  5:nestedfunc_out_ff_5"                                        +"\n"+
		                        "  0-0->1"                                        +"\n"+
		                        "  1-1->2"                                        +"\n"+
		                        "  2-T_2->3"                                        +"\n"+
		                        "  2-F_3->4"                                        +"\n"+
		                        "  4-4->5"                                        +"\n"+
		                        "  3-5->5"                                        +"\n"+
		                    "}"
		                    ,
		                    },
		    /////////////////  32   ///////////////////	
		                    {
		                    "int i;"                                                               +"\n"+
		                    "f(){"                                                                 +"\n"+
		                    " int ff(int i){"                                                      +"\n"+
		                    "	i=1;"                                                                +"\n"+
		                    "	while(i>1)"                                                          +"\n"+
		                    "	{"                                                                   +"\n"+
		                    "	  i--;"                                                              +"\n"+
		                    "	  if(i>1)	goto label;"                                               +"\n"+
		                    "	  else break;"                                                       +"\n"+
		                    "	}"                                                                   +"\n"+
		                    "	label:"                                                              +"\n"+
		                    "	  i=100;"                                                            +"\n"+
		                    " }"                                                                   +"\n"+
		                    " int j=1;"                                                            +"\n"+
		                    " if(j>0)"                                                             +"\n"+
		                    "	return j;"                                                           +"\n"+
		                    "}"                                                                    
		                    ,
		                    "gcc"
		                    ,
		                    "//FunctionDefinition"
		                    ,
		                    "Graph {"                                                        +"\n"+
		                        "  0:func_head_f_0"                                        +"\n"+
		                        "  1:decl_stmt_1"                                        +"\n"+
		                        "  2:if_head_2"                                        +"\n"+
		                        "  3:return_3"                                        +"\n"+
		                        "  4:if_out_4"                                        +"\n"+
		                        "  5:func_out_f_5"                                        +"\n"+
		                        "  0-0->1"                                        +"\n"+
		                        "  1-1->2"                                        +"\n"+
		                        "  2-T_2->3"                                        +"\n"+
		                        "  2-F_3->4"                                        +"\n"+
		                        "  4-4->5"                                        +"\n"+
		                        "  3-5->5"                                        +"\n"+
		                    "}"
		                    ,
		                    },










	            
	            
		});
	}
}
