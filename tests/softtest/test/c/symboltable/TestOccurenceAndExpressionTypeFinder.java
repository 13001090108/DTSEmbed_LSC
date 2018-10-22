package softtest.test.c.symboltable;

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
import softtest.symboltable.c.OccurrenceAndExpressionTypeFinder;
import softtest.symboltable.c.ScopeAndDeclarationFinder;
import softtest.symboltable.c.Type.CType;
import softtest.tools.c.jaxen.MatchesFunction;

@RunWith(Parameterized.class)
public class TestOccurenceAndExpressionTypeFinder
{
	private String source = null;
	private String compiletype=null;
	private String expr = null;
	private String type = null;
	
	public TestOccurenceAndExpressionTypeFinder(String source,String compiletype, String expr, String type) {
		this.source = source;
		this.compiletype=compiletype;
		this.expr = expr;
		this.type = type;
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
			String typestring="";
			try {
				m = eb.getClass().getMethod("getType");
				if(m!=null){
					CType type=(CType) m.invoke(eb);
					if(type!=null){
						typestring=type.toString();
					}
				}
			} catch (Exception e) {
				e.printStackTrace();
			} 		
			assertEquals(""+CParser.getType()+" type error",type,typestring);
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
	            "int fun();"                                                           +"\n"+
	            "typeof(fun()) i=3;"                                                   
	            ,
	            "gcc"
	            ,
	            "//AssignmentExpression[@BeginColumn='8']"
	            ,
	            "int"
	            ,
	            },
/////////////////  1   ///////////////////	
	            {
	            "f()"                                                                  +"\n"+
	            "{"                                                                    +"\n"+
	            "	printf(\"\");"                                                         +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//PostfixExpression"
	            ,
	            "int"
	            ,
	            },
/////////////////  2   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "	int *p;"                                                             +"\n"+
	            "	p++;"                                                                +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//Expression"
	            ,
	            "*int"
	            ,
	            },
/////////////////  3   ///////////////////	
	            {
	            "void f(){"                                                            +"\n"+
	            "	float i=3+4;"                                                        +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//AdditiveExpression"
	            ,
	            "int"
	            ,
	            },
/////////////////  4   ///////////////////	
	            {
	            "void f(){"                                                            +"\n"+
	            "	float i=3+4-5;"                                                      +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//AdditiveExpression"
	            ,
	            "int"
	            ,
	            },
/////////////////  5   ///////////////////	
	            {
	            "void f(){"                                                            +"\n"+
	            "	float *i=0;"                                                         +"\n"+
	            "	i=i+1;"                                                              +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//AdditiveExpression"
	            ,
	            "*float"
	            ,
	            },           
/////////////////  6   ///////////////////	
	            {
	            "void f(){"                                                            +"\n"+
	            "	float *i=0;"                                                         +"\n"+
	            "	i=1+i;"                                                              +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//AdditiveExpression"
	            ,
	            "*float"
	            ,
	            },
/////////////////  7   ///////////////////	
	            {
	            "void f(){"                                                            +"\n"+
	            "	long double d1=3.0;"                                                 +"\n"+
	            "	int i=d1+3;"                                                         +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//AdditiveExpression"
	            ,
	            "long double"
	            ,
	            },
/////////////////  8   ///////////////////	
	            {
	            "void f(){"                                                            +"\n"+
	            "	double d1=3.0;"                                                      +"\n"+
	            "	int i=d1+3;"                                                         +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//AdditiveExpression"
	            ,
	            "double"
	            ,
	            },
/////////////////  9   ///////////////////	
	            {
	            "void f(){"                                                            +"\n"+
	            "	float d1=3.0;"                                                       +"\n"+
	            "	int i=d1+3;"                                                         +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//AdditiveExpression"
	            ,
	            "float"
	            ,
	            },
/////////////////  10   ///////////////////	
	            {
	            "void f(){"                                                            +"\n"+
	            "	long long d1=3;"                                                     +"\n"+
	            "	int i=d1+1;"                                                         +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//AdditiveExpression"
	            ,
	            "long long"
	            ,
	            },
/////////////////  11   ///////////////////	
	            {
	            "void f(){"                                                            +"\n"+
	            "	unsigned long d1=3;"                                                 +"\n"+
	            "	int i=d1+1;"                                                         +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//AdditiveExpression"
	            ,
	            "unsigned long"
	            ,
	            },
/////////////////  12   ///////////////////	
	            {
	            "void f(){"                                                            +"\n"+
	            "	unsigned int d1=3;"                                                  +"\n"+
	            "	int i=d1+1u;"                                                        +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//AdditiveExpression"
	            ,
	            "unsigned int"
	            ,
	            },
/////////////////  13   ///////////////////	
	            {
	            "void f(){"                                                            +"\n"+
	            "	long d1=3,d2;"                                                       +"\n"+
	            "	int i=d1+3;"                                                         +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//AdditiveExpression"
	            ,
	            "long"
	            ,
	            },
/////////////////  14   ///////////////////	
	            {
	            "void f(){"                                                            +"\n"+
	            "	int i=1;"                                                            +"\n"+
	            "	int j=i&3;"                                                          +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//ANDExpression"
	            ,
	            "int"
	            ,
	            },
/////////////////  15   ///////////////////	
	            {
	            "void f(){"                                                            +"\n"+
	            "	long k=(long)(2+3);"                                                 +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//CastExpression"
	            ,
	            "long"
	            ,
	            },
/////////////////  16   ///////////////////	
	            {
	            "void f(){"                                                            +"\n"+
	            "	int i=(3==2)?1:2;"                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//ConditionalExpression"
	            ,
	            "int"
	            ,
	            },
/////////////////  17   ///////////////////	
	            {
	            "void f(){"                                                            +"\n"+
	            "	char *str=\"abc\";"                                                    +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//Constant"
	            ,
	            "*char"
	            ,
	            },
/////////////////  18   ///////////////////	
	            {
	            "void f(){"                                                            +"\n"+
	            "	char c='a';"                                                         +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//Constant"
	            ,
	            "char"
	            ,
	            },
/////////////////  19   ///////////////////	
	            {
	            "void f(){"                                                            +"\n"+
	            "	unsigned long i=5ul;"                                                +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//Constant"
	            ,
	            "unsigned long"
	            ,
	            },
/////////////////  20   ///////////////////	
	            {
	            "unsigned long long int ij;"                                           +"\n"+
	            "int i=ij+3;"                                                          
	            ,
	            "all"
	            ,
	            "//AdditiveExpression"
	            ,
	            "unsigned long long"
	            ,
	            },

/////////////////  21   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "int i=0;"                                                             +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//Constant"
	            ,
	            "int"
	            ,
	            },
/////////////////  22   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "int i=0x5f;"                                                          +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//Constant"
	            ,
	            "int"
	            ,
	            },
/////////////////  23   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "int i=057;"                                                           +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//Constant"
	            ,
	            "int"
	            ,
	            },
/////////////////  24   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "int i=57;"                                                           +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//Constant"
	            ,
	            "int"
	            ,
	            },
/////////////////  25   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "float i=3.0f;"                                                        +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//Constant"
	            ,
	            "float"
	            ,
	            },
/////////////////  26   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "float i=3.0;"                                                        +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//Constant"
	            ,
	            "double"
	            ,
	            },
/////////////////  27   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "int a[1];"                                                            +"\n"+
	            "a[0]=1;"                                                              +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//ConstantExpression"
	            ,
	            "int"
	            ,
	            },
/////////////////  28   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "int i=1;"                                                             +"\n"+
	            "if(i==1);"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//EqualityExpression"
	            ,
	            "bool"
	            ,
	            },
/////////////////  29   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "int i=1;"                                                             +"\n"+
	            "if(i | 1);"                                                           +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//InclusiveORExpression"
	            ,
	            "int"
	            ,
	            },
/////////////////  30   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "int i=1;"                                                             +"\n"+
	            "if(i && 1);"                                                          +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//LogicalANDExpression"
	            ,
	            "bool"
	            ,
	            },
/////////////////  31   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "int i=1;"                                                             +"\n"+
	            "if(i || 1);"                                                          +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//LogicalORExpression"
	            ,
	            "bool"
	            ,
	            },
/////////////////  32   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "int i=1;"                                                             +"\n"+
	            "i=3%5;"                                                               +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//MultiplicativeExpression"
	            ,
	            "int"
	            ,
	            },
/////////////////  33   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "int a[1];"                                                            +"\n"+
	            ""                                                                     +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//PostfixExpression"
	            ,
	            "int"
	            ,
	            },
/////////////////  34   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "int a[1],*p;"                                                         +"\n"+
	            "p=a;"                                                                 +"\n"+
	            "p[0]=1;"                                                              +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//PostfixExpression[@BeginLine='3'][@BeginColumn='1']"
	            ,
	            "*int"
	            ,
	            },
/////////////////  35   ///////////////////	
	            {
	            "char fun();"                                                          +"\n"+
	            "f(){"                                                                 +"\n"+
	            "int i=fun();"                                                         +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//PostfixExpression"
	            ,
	            "char"
	            ,
	            },
/////////////////  36   ///////////////////	
	            {
	            "struct {double f;}s;"                                                 +"\n"+
	            "void f(int i){"                                                       +"\n"+
	            "	int j=s.f;"                                                          +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//PostfixExpression"
	            ,
	            "double"
	            ,
	            },
/////////////////  37   ///////////////////	
	            {
	            "struct {double f;}*s;"                                                +"\n"+
	            "f(){"                                                                 +"\n"+
	            "int i=s->f;"                                                          +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//PostfixExpression"
	            ,
	            "double"
	            ,
	            },
/////////////////  38   ///////////////////	
	            {
	            "struct {double *f;}*s;"                                               +"\n"+
	            "f(){"                                                                 +"\n"+
	            "int i=s->f;"                                                          +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//PostfixExpression"
	            ,
	            "*double"
	            ,
	            },
/////////////////  39   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "int i=3>>2;"                                                          +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//ShiftExpression"
	            ,
	            "int"
	            ,
	            },
/////////////////  40   ///////////////////	
	            {
	            "long fun();"                                                          +"\n"+
	            "f(){"                                                                 +"\n"+
	            "typeof(fun()) i;"                                                     +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "//Declarator[@Image='i']"
	            ,
	            "long"
	            ,
	            },
/////////////////  41   ///////////////////	
	            {
	            "int i=0xA3ul;"                                                        
	            ,
	            "all"
	            ,
	            "//Constant"
	            ,
	            "unsigned long"
	            ,
	            },
/////////////////  42   ///////////////////	
	            {
	            "float f(char c);"                                                     +"\n"+
	            "fun(){"                                                               +"\n"+
	            "int i=f(1)+1;"                                                        +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//PostfixExpression[@BeginColumn='9']"
	            ,
	            "int"
	            ,
	            },
/////////////////  43   ///////////////////	
	            {
	            "int i=3>2;"                                                           
	            ,
	            "all"
	            ,
	            "//RelationalExpression"
	            ,
	            "bool"
	            ,
	            },
/////////////////  44   ///////////////////	
	            {
	            "unsigned j=4;"                                                        +"\n"+
	            "int i=j>>1;"                                                          
	            ,
	            "all"
	            ,
	            "//ShiftExpression"
	            ,
	            "unsigned int"
	            ,
	            },
/////////////////  45   ///////////////////	
	            {
	            "unsigned j=4;"                                                        +"\n"+
	            "int i=++j;"                                                           
	            ,
	            "all"
	            ,
	            "//UnaryExpression[@BeginColumn='7']"
	            ,
	            "unsigned int"
	            ,
	            },
/////////////////  46   ///////////////////	
	            {
	            "unsigned j=4;"                                                        +"\n"+
	            "int i=&j;"                                                            
	            ,
	            "all"
	            ,
	            "//UnaryExpression[@BeginColumn='7']"
	            ,
	            "const *unsigned int"
	            ,
	            },
/////////////////  47   ///////////////////	
	            {
	            "int j=10;"                                                            +"\n"+
	            "int *i=&j;"                                                           +"\n"+
	            "int k=*i;"                                                            
	            ,
	            "all"
	            ,
	            "//UnaryExpression[@BeginColumn='7'][@BeginLine='3']"
	            ,
	            "int"
	            ,
	            },
/////////////////  48   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "__label__ lab;"                                                       +"\n"+
	            "void *ptr=&&a; "                                                      +"\n"+
	            "goto *ptr;"                                                           +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "//UnaryExpression[@BeginColumn='11']"
	            ,
	            "unsigned int"
	            ,
	            },
/////////////////  49   ///////////////////	
	            {
	            "int i=+5;"                                                            +"\n"+
	            "int j=-2;"                                                            +"\n"+
	            "int k=~i;"                                                            +"\n"+
	            "int m=!j;"                                                            
	            ,
	            "all"
	            ,
	            "//UnaryExpression[@BeginLine='1'][@BeginColumn='7']"
	            ,
	            "int"
	            ,
	            },
/////////////////  50   ///////////////////	
	            {
	            "int i=+5;"                                                            +"\n"+
	            "int j=-2;"                                                            +"\n"+
	            "int k=~i;"                                                            +"\n"+
	            "int m=!j;"                                                            
	            ,
	            "all"
	            ,
	            "//UnaryExpression[@BeginLine='2'][@BeginColumn='7']"
	            ,
	            "int"
	            ,
	            },
/////////////////  51   ///////////////////	
	            {
	            "int i=+5;"                                                            +"\n"+
	            "int j=-2;"                                                            +"\n"+
	            "int k=~i;"                                                            +"\n"+
	            "int m=!j;"                                                            
	            ,
	            "all"
	            ,
	            "//UnaryExpression[@BeginLine='3'][@BeginColumn='7']"
	            ,
	            "int"
	            ,
	            },
/////////////////  52   ///////////////////	
	            {
	            "int i=+5;"                                                            +"\n"+
	            "int j=-2;"                                                            +"\n"+
	            "int k=~i;"                                                            +"\n"+
	            "int m=!j;"                                                            
	            ,
	            "all"
	            ,
	            "//UnaryExpression[@BeginLine='4'][@BeginColumn='7']"
	            ,
	            "bool"
	            ,
	            },
/////////////////  53   ///////////////////	
	            {
	            "int i=sizeof(int);"                                                   
	            ,
	            "all"
	            ,
	            "//UnaryExpression"
	            ,
	            "unsigned int"
	            ,
	            },
/////////////////  54   ///////////////////	
	            {
	            "int i=__alignof__(int);"                                              
	            ,
	            "gcc"
	            ,
	            "//UnaryExpression"
	            ,
	            "unsigned int"
	            ,
	            },
/////////////////  55   ///////////////////	
	            {
	            "int f();"                                                             +"\n"+
	            "typeof(f()+3.0) i;"                                                   
	            ,
	            "gcc"
	            ,
	            "//Declarator"
	            ,
	            "double"
	            ,
	            },
/////////////////  56   ///////////////////	
	            {
	            "int i=0x0F;"                                                          
	            ,
	            "all"
	            ,
	            "//Constant"
	            ,
	            "int"
	            ,
	            },
/////////////////  57   ///////////////////	
	            {
	            "int i=00;"                                                        
	            ,
	            "all"
	            ,
	            "//Constant"
	            ,
	            "int"
	            ,
	            },
/////////////////  58   ///////////////////	
	            {
	            "int i=1^3;"                                                           
	            ,
	            "all"
	            ,
	            "//ExclusiveORExpression"
	            ,
	            "int"
	            ,
	            },
/////////////////  59   ///////////////////	
	            {
	            "int i=({"                                                             +"\n"+
	            "	char a[]=\"abc\";"                                                     +"\n"+
	            "	*(a+1);"                                                             +"\n"+
	            "});"                                                                  
	            ,
	            "gcc"
	            ,
	            "//AssignmentExpression[@BeginLine='1']"
	            ,
	            "char"
	            ,
	            },
/////////////////  60   ///////////////////	
	            {
	            "void (*p)();"                                                         +"\n"+
	            "void f(){}"                                                           +"\n"+
	            "void m(){"                                                            +"\n"+
	            "p=&f;"                                                                +"\n"+
	            "p();"                                                                 +"\n"+
	            "(*p)();"                                                              +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//UnaryExpression[@BeginFileLine='6'][@BeginColumn='2']"
	            ,
	            "()void"
	            ,
	            },
/////////////////  61:zys	2011.6.17	之前的版本将局部变量的引用当作了函数调用   ///////////////////	
	            {
	            "void f();"                                                            +"\n"+
	            "void g(){"                                                            +"\n"+
	            "	int f=0;"                                                            +"\n"+
	            "	int i=f;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "//PrimaryExpression[@Method='false'][@BeginLine='4']"
	            ,
	            "int"
	            ,
	            },
/////////////////  62:zys 2011.6.24 malloc printf等库函数可以在无函数原型时任意调用，因此节点类型应该取库函数返回值类型///////////////////	
	            {
	            "typedef struct _ST {"                                                 +"\n"+
	            "    int a;"                                                           +"\n"+
	            "}ST;"                                                                 +"\n"+
	            ""                                                                     +"\n"+
	            "int func(ST* st)"                                                     +"\n"+
	            "{"                                                                    +"\n"+
	            "    ST *sa = (ST*)malloc(sizeof(ST));"                                +"\n"+
	            "    if (sa != NULL ) {"                                               +"\n"+
	            "       sa->a = 1; //FP,NPD"                                           +"\n"+
	            "       return 1;"                                                     +"\n"+
	            "    }"                                                                +"\n"+
	            "    return 0;"                                                        +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//CastExpression"
	            ,
	            "*ST:struct _ST"
	            ,
	            },
/////////////////  63:zys 2011.6.24 malloc printf等库函数可以在无函数原型时任意调用，
/////////////////	因此节点类型应该取库函数返回值类型;该回归中未生成函数摘要，因此类型为默认值 int///////////////////	
	            {
	            "typedef struct _ST {"                                                 +"\n"+
	            "    int a;"                                                           +"\n"+
	            "}ST;"                                                                 +"\n"+
	            ""                                                                     +"\n"+
	            "int func(ST* st)"                                                     +"\n"+
	            "{"                                                                    +"\n"+
	            "    ST *sa = (ST*)malloc(sizeof(ST));"                                +"\n"+
	            "    if (sa != NULL ) {"                                               +"\n"+
	            "       sa->a = 1; //FP,NPD"                                           +"\n"+
	            "       return 1;"                                                     +"\n"+
	            "    }"                                                                +"\n"+
	            "    return 0;"                                                        +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//PostfixExpression[@BeginLine='7'][@BeginColumn='19']"
	            ,
	            "int"
	            ,
	            },
/////////////////  64:zys 2011.6.24 sizeof的类型
	            {
	            "typedef struct _ST {"                                                 +"\n"+
	            "    int a;"                                                           +"\n"+
	            "}ST;"                                                                 +"\n"+
	            ""                                                                     +"\n"+
	            "int func(ST* st)"                                                     +"\n"+
	            "{"                                                                    +"\n"+
	            "    ST *sa = (ST*)malloc(sizeof(ST));"                                +"\n"+
	            "    if (sa != NULL ) {"                                               +"\n"+
	            "       sa->a = 1; //FP,NPD"                                           +"\n"+
	            "       return 1;"                                                     +"\n"+
	            "    }"                                                                +"\n"+
	            "    return 0;"                                                        +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//AssignmentExpression[@BeginLine='7'][@BeginColumn='26']"
	            ,
	            "unsigned int"
	            ,
	            },
	            
	            
		});
	}
}
