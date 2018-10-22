package softtest.test.c.defuseanalysis;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.io.ByteArrayInputStream;
import java.util.Arrays;
import java.util.Collection;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;

import org.junit.After;
import org.junit.AfterClass;
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
import softtest.cfg.c.ControlFlowVisitor;
import softtest.cfg.c.Graph;
import softtest.symboltable.c.AbstractScope;
import softtest.symboltable.c.OccurrenceAndExpressionTypeFinder;
import softtest.symboltable.c.ScopeAndDeclarationFinder;
import softtest.tools.c.jaxen.MatchesFunction;

@RunWith(Parameterized.class)
public class TestDUAnalysisVisitor
{
	private String source = null;
	private String compiletype=null;
	private String defuse = null;
	public TestDUAnalysisVisitor(String source,String compiletype, String expr,String type) {
		this.source = source;
		this.compiletype=compiletype;
		this.defuse = type;
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
		astroot.jjtAccept(new DUAnalysisVisitor(), null);
		
		List functionList=astroot.findChildrenOfType(ASTFunctionDefinition.class);
		String result="";
		//String test="";
		for(Iterator i=functionList.iterator();i.hasNext();)
		{
			ASTFunctionDefinition function=(ASTFunctionDefinition)i.next();
			Graph g=function.getGraph();
			result+=g.printForDefUse();
			//test+=g.printGraphForTestCaseGeneratorForDUAnalysis();
			if(i.hasNext())
			{
				result+="\n";
				//test+="\n";
			}
		}
		//System.out.println(defuse);
		//System.out.println(result);
		//System.out.println(test);
		assertEquals("DefUseAnalysisVisitor Error!",defuse,result);
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
	            "int i=1;"                                                             +"\n"+
	            "int j=2;"                                                             +"\n"+
	            "void f()"                                                             +"\n"+
	            "{"                                                                    +"\n"+
	            "	i=3;"                                                                +"\n"+
	            "	int k=4;"                                                            +"\n"+
	            "	k=4;"                                                                +"\n"+
	            "	if(k>3 && i<10)"                                                     +"\n"+
	            "		{"                                                                  +"\n"+
	            "			k++;"                                                              +"\n"+
	            "			++i;"                                                              +"\n"+
	            "		}"                                                                  +"\n"+
	            "	j--;"                                                                +"\n"+
	            "}"                                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "int main()"                                                           +"\n"+
	            "{"                                                                    +"\n"+
	            "	i=100;"                                                              +"\n"+
	            "	if(i>50)"                                                            +"\n"+
	            "		j=i+1;"                                                             +"\n"+
	            "	printf(j);"                                                          +"\n"+
	            "	return 0;"                                                           +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "TranslationUnit"
	            ,
	            "Graph {"                                                        +"\n"+
	                "  func_head_f_0:"                                        +"\n"+
	                "  stmt_1:   i:(DEF) [5Line,2Column]"                                        +"\n"+
	                "  decl_stmt_2:   k:(DEF) [6Line,6Column]   i:(DEF) [5Line,2Column]"                                        +"\n"+
	                "  stmt_3:   k:(DEF) [7Line,2Column]   i:(DEF) [5Line,2Column]"                                        +"\n"+
	                "  if_head_4:   k:(DEF) [7Line,2Column]   i:(DEF) [5Line,2Column]"                                        +"\n"+
	                "  stmt_5:   k:(DEF_AFTER_USE) [10Line,4Column]   i:(DEF) [5Line,2Column]"                                        +"\n"+
	                "  stmt_6:   k:(DEF_AFTER_USE) [10Line,4Column]   i:(DEF_AFTER_USE) [11Line,6Column]"                                        +"\n"+
	                "  if_out_7:   k:(DEF) [7Line,2Column](DEF_AFTER_USE) [10Line,4Column]   i:(DEF) [5Line,2Column](DEF_AFTER_USE) [11Line,6Column]"                                        +"\n"+
	                "  stmt_8:   k:(DEF) [7Line,2Column](DEF_AFTER_USE) [10Line,4Column]   j:(DEF_AFTER_USE) [13Line,2Column]   i:(DEF) [5Line,2Column](DEF_AFTER_USE) [11Line,6Column]"                                        +"\n"+
	                "  func_out_f_9:   k:(DEF) [7Line,2Column](DEF_AFTER_USE) [10Line,4Column]   j:(DEF_AFTER_USE) [13Line,2Column]   i:(DEF) [5Line,2Column](DEF_AFTER_USE) [11Line,6Column]"                                        +"\n"+
	            "}"+"\n"+
	"Graph {"                                                        +"\n"+
	                "  func_head_main_0:"                                        +"\n"+
	                "  stmt_1:   i:(DEF) [18Line,2Column]"                                        +"\n"+
	                "  if_head_2:   i:(DEF) [18Line,2Column]"                                        +"\n"+
	                "  stmt_3:   j:(DEF) [20Line,3Column]   i:(DEF) [18Line,2Column]"                                        +"\n"+
	                "  if_out_4:   j:(DEF) [20Line,3Column]   i:(DEF) [18Line,2Column]"                                        +"\n"+
	                "  stmt_5:   j:(DEF) [20Line,3Column]   i:(DEF) [18Line,2Column]"                                        +"\n"+
	                "  return_6:   j:(DEF) [20Line,3Column]   i:(DEF) [18Line,2Column]"                                        +"\n"+
	                "  func_out_main_7:   j:(DEF) [20Line,3Column]   i:(DEF) [18Line,2Column]"                                        +"\n"+
	            "}"
	            ,
	            },
/////////////////  1   ///////////////////	
	            {
	            "int i=3;"                                                             +"\n"+
	            "int j=i;"                                                             +"\n"+
	            "void f(){"                                                            +"\n"+
	            "	int j;"                                                              +"\n"+
	            "	j++;"                                                                +"\n"+
	            "	--j;"                                                                +"\n"+
	            "	float f;"                                                            +"\n"+
	            "	if(j>0){j=1;}"                                                       +"\n"+
	            "	if(f>3.0){f=1.0;}"                                                   +"\n"+
	            "	i*=3;"                                                               +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "TranslationUnit"
	            ,
	            "Graph {"                                                        +"\n"+
	                "  func_head_f_0:"                                        +"\n"+
	                "  decl_stmt_1:"                                        +"\n"+
	                "  stmt_2:   j:(DEF_AFTER_USE) [5Line,2Column]"                                        +"\n"+
	                "  stmt_3:   j:(DEF_AFTER_USE) [6Line,4Column]"                                        +"\n"+
	                "  decl_stmt_4:   j:(DEF_AFTER_USE) [6Line,4Column]"                                        +"\n"+
	                "  if_head_5:   j:(DEF_AFTER_USE) [6Line,4Column]"                                        +"\n"+
	                "  stmt_6:   j:(DEF) [8Line,10Column]"                                        +"\n"+
	                "  if_out_7:   j:(DEF_AFTER_USE) [6Line,4Column](DEF) [8Line,10Column]"                                        +"\n"+
	                "  if_head_8:   j:(DEF_AFTER_USE) [6Line,4Column](DEF) [8Line,10Column]"                                        +"\n"+
	                "  stmt_9:   j:(DEF_AFTER_USE) [6Line,4Column](DEF) [8Line,10Column]   f:(DEF) [9Line,12Column]"                                        +"\n"+
	                "  if_out_10:   j:(DEF_AFTER_USE) [6Line,4Column](DEF) [8Line,10Column]   f:(DEF) [9Line,12Column]"                                        +"\n"+
	                "  stmt_11:   j:(DEF_AFTER_USE) [6Line,4Column](DEF) [8Line,10Column]   i:(DEF) [10Line,2Column]   f:(DEF) [9Line,12Column]"                                        +"\n"+
	                "  func_out_f_12:   j:(DEF_AFTER_USE) [6Line,4Column](DEF) [8Line,10Column]   i:(DEF) [10Line,2Column]   f:(DEF) [9Line,12Column]"                                        +"\n"+
	            "}"
	            ,
	            },
/////////////////  2   ///////////////////	
	            {
	            "int i=3;"                                                             +"\n"+
	            "int j=i;"                                                             +"\n"+
	            "void f(){"                                                            +"\n"+
	            "	int j;"                                                              +"\n"+
	            "	j++;"                                                                +"\n"+
	            "	--j;"                                                                +"\n"+
	            "	float f;"                                                            +"\n"+
	            "	if(j>0){j=1;}"                                                       +"\n"+
	            "	if(f>3.0){f=1.0;}"                                                   +"\n"+
	            "	i*=3;"                                                               +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "TranslationUnit"
	            ,
	            "Graph {"                                                        +"\n"+
	                "  func_head_f_0:"                                        +"\n"+
	                "  decl_stmt_1:"                                        +"\n"+
	                "  stmt_2:   j:(DEF_AFTER_USE) [5Line,2Column]"                                        +"\n"+
	                "  stmt_3:   j:(DEF_AFTER_USE) [6Line,4Column]"                                        +"\n"+
	                "  decl_stmt_4:   j:(DEF_AFTER_USE) [6Line,4Column]"                                        +"\n"+
	                "  if_head_5:   j:(DEF_AFTER_USE) [6Line,4Column]"                                        +"\n"+
	                "  stmt_6:   j:(DEF) [8Line,10Column]"                                        +"\n"+
	                "  if_out_7:   j:(DEF_AFTER_USE) [6Line,4Column](DEF) [8Line,10Column]"                                        +"\n"+
	                "  if_head_8:   j:(DEF_AFTER_USE) [6Line,4Column](DEF) [8Line,10Column]"                                        +"\n"+
	                "  stmt_9:   j:(DEF_AFTER_USE) [6Line,4Column](DEF) [8Line,10Column]   f:(DEF) [9Line,12Column]"                                        +"\n"+
	                "  if_out_10:   j:(DEF_AFTER_USE) [6Line,4Column](DEF) [8Line,10Column]   f:(DEF) [9Line,12Column]"                                        +"\n"+
	                "  stmt_11:   j:(DEF_AFTER_USE) [6Line,4Column](DEF) [8Line,10Column]   i:(DEF) [10Line,2Column]   f:(DEF) [9Line,12Column]"                                        +"\n"+
	                "  func_out_f_12:   j:(DEF_AFTER_USE) [6Line,4Column](DEF) [8Line,10Column]   i:(DEF) [10Line,2Column]   f:(DEF) [9Line,12Column]"                                        +"\n"+
	            "}"
	            ,
	            },







	
		});
	}
}
