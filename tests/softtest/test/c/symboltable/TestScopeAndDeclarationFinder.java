package softtest.test.c.symboltable;

import static org.junit.Assert.*;

import java.io.*;
import java.util.*;
import java.lang.reflect.*;

import softtest.ast.c.*;
import softtest.symboltable.c.*;
import softtest.symboltable.c.Type.CType;
import softtest.tools.c.jaxen.*;

import org.jaxen.JaxenException;
import org.junit.*;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;


@RunWith(Parameterized.class)
public class TestScopeAndDeclarationFinder {
	private String source = null;
	private String compiletype=null;
	private String expr = null;
	private String type = null;
	
	public TestScopeAndDeclarationFinder(String source,String compiletype, String expr, String type) {
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
	            "int i;"                                                               
	            ,
	            "all"
	            ,
	            "//Declarator"
	            ,
	            "int"
	            ,
	            },
/////////////////  1   ///////////////////	
	            {
	            "int i,j,k[10];"                                                       
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='k']"
	            ,
	            "[10]int"
	            ,
	            },      
/////////////////  2   ///////////////////	
	            {
	            "int i,j,k[10][9][6];"                                               
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='k']"
	            ,
	            "[10][9][6]int"
	            ,
	            },
/////////////////  3   ///////////////////	
	            {
	            "int *i;"                                                              
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='i']"
	            ,
	            "*int"
	            ,
	            },        
/////////////////  4   ///////////////////	
	            {
	            "int **i;"                                                             
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='i']"
	            ,
	            "**int"
	            ,
	            },
/////////////////  5   ///////////////////	
	            {
	            "int i,**j;"                                                           
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='j']"
	            ,
	            "**int"
	            ,
	            },  
/////////////////  6   ///////////////////	
	            {
	            "int *i[10];"                                                          
	            ,
	            "all"
	            ,
	            "//Declarator"
	            ,
	            "[10]*int"
	            ,
	            },
/////////////////  7   ///////////////////	
	            {
	            "int (*i)[10];"                                                        
	            ,
	            "all"
	            ,
	            "//Declarator"
	            ,
	            "*[10]int"
	            ,
	            },
/////////////////  8   ///////////////////	
	            {
	            "int *(*i[10])[10];"                                                   
	            ,
	            "all"
	            ,
	            "//Declarator"
	            ,
	            "[10]*[10]*int"
	            ,
	            },
/////////////////  9   ///////////////////	
	            {
	            "int f();"                                                             
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f()int"
	            ,
	            },
/////////////////  10   ///////////////////	
	            {
	            "void *f();"                                                           
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f()*void"
	            ,
	            },
/////////////////  11   ///////////////////	
	            {
	            "void (*f())();"                                                       
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f()*()void"
	            ,
	            },
/////////////////  12   ///////////////////	
	            {
	            "int f(int i);"                                                        
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int)int"
	            ,
	            },
/////////////////  13   ///////////////////	
	            {
	            "int f(int i,double f);"                                               
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int,double)int"
	            ,
	            },  
/////////////////  14   ///////////////////	
	            {
	            "int f(int i,double f,...);"                                           
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int,double,...)int"
	            ,
	            },       
/////////////////  15   ///////////////////	
	            {
	            "f();"                                                                 
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f()int"
	            ,
	            },
/////////////////  16   ///////////////////	
	            {
	            "f(int i);"                                                            
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int)int"
	            ,
	            },
/////////////////  17   ///////////////////	
	            {
	            "f(int i,...);"                                                        
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int,...)int"
	            ,
	            },
/////////////////  18   ///////////////////	
	            {
	            "void f(int,...);"                                                     
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int,...)void"
	            ,
	            },
/////////////////  19   ///////////////////	
	            {
	            "void f(int i,void *j);"                                               
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int,*void)void"
	            ,
	            },
/////////////////  20   ///////////////////	
	            {
	            "void f(int i,double j,float i[]);"                                    
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int,double,[]float)void"
	            ,
	            },
/////////////////  21   ///////////////////	
	            {
	            "void f(int i,double j,float *i[]);"                                   
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int,double,[]*float)void"
	            ,
	            },
/////////////////  22   ///////////////////	
	            {
	            "void f(int i,double j,float (*i)[]);"                                 
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int,double,*[]float)void"
	            ,
	            },
/////////////////  23   ///////////////////	
	            {
	            "void f(int i,double j,float (*i)());"                                 
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int,double,*()float)void"
	            ,
	            },
/////////////////  24   ///////////////////	
	            {
	            "void f(int i,double j,float (*i())());"                               
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int,double,()*()float)void"
	            ,
	            },
/////////////////  25   ///////////////////	
	            {
	            "void f(int i,double j,float (*i)()());"                               
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int,double,*()()float)void"
	            ,
	            },
///////////////// 26   ///////////////////	
	            {
	            "void f(int i,double j,float (*i)(int l)());"                          
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int,double,*(int)()float)void"
	            ,
	            },
/////////////////  27   ///////////////////	
	            {
	            "void f(int);"                                                         
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int)void"
	            ,
	            },
/////////////////  28   ///////////////////	
	            {
	            "void f(int,double);"                                                  
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int,double)void"
	            ,
	            },
///////////////// 29   ///////////////////	
	            {
	            "void f(int,double,float);"                                            
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int,double,float)void"
	            ,
	            },
/////////////////  30   ///////////////////	
	            {
	            "void f(int,double,float*);"                                           
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int,double,*float)void"
	            ,
	            },
/////////////////  31   ///////////////////	
	            {
	            "void f(int,double,float[]);"                                          
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int,double,[]float)void"
	            ,
	            },
/////////////////  32   ///////////////////	
	            {
	            "void f(int,double,float[10]);"                                        
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int,double,[10]float)void"
	            ,
	            },
/////////////////  33   ///////////////////	
	            {
	            "void f(int,double,float(*)[10]);"                                     
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int,double,*[10]float)void"
	            ,
	            },
/////////////////  34   ///////////////////	
	            {
	            "void f(int,double,float*[10]);"                                       
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int,double,[10]*float)void"
	            ,
	            },
/////////////////  35   ///////////////////	
	            {
	            "void f(int,double,float**[10]);"                                      
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int,double,[10]**float)void"
	            ,
	            },
/////////////////  36   ///////////////////	
	            {
	            "void f(int,double,float*(*)[10]);"                                    
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int,double,*[10]*float)void"
	            ,
	            },
/////////////////  37   ///////////////////	
	            {
	            "void f(int,double,float*());"                                         
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int,double,()*float)void"
	            ,
	            },
/////////////////  38   ///////////////////	
	            {
	            "void f(int,double,float*(int));"                                      
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int,double,(int)*float)void"
	            ,
	            },
///////////////// 39   ///////////////////	
	            {
	            "void f(int,double,float*(int,double));"                               
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int,double,(int,double)*float)void"
	            ,
	            },
/////////////////  40   ///////////////////	
	            {
	            "void f(int,double,float(*)(int,double));"                             
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int,double,*(int,double)float)void"
	            ,
	            },
/////////////////  41   ///////////////////	
	            {
	            "void* f()();"                                                         
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f()()*void"
	            ,
	            },
/////////////////  42   ///////////////////	
	            {
	            "void* f(float)(int);"                                                 
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(float)(int)*void"
	            ,
	            },            
/////////////////  43   ///////////////////	
	            {
	            "void f(){}"                                                           
	            ,
	            "all"
	            ,
	            "//FunctionDefinition"
	            ,
	            "f()void"
	            ,
	            },
/////////////////  44   ///////////////////	
	            {
	            "void* f(){}"                                                          
	            ,
	            "all"
	            ,
	            "//FunctionDefinition"
	            ,
	            "f()*void"
	            ,
	            },
/////////////////  45   ///////////////////	
	            {
	            "void** f(){}"                                                         
	            ,
	            "all"
	            ,
	            "//FunctionDefinition"
	            ,
	            "f()**void"
	            ,
	            },
/////////////////  46   ///////////////////	
	            {
	            "void (*f())(){}"                                                      
	            ,
	            "all"
	            ,
	            "//FunctionDefinition"
	            ,
	            "f()*()void"
	            ,
	            },
/////////////////  47   ///////////////////	
	            {
	            "int* (*f())(){}"                                                      
	            ,
	            "all"
	            ,
	            "//FunctionDefinition"
	            ,
	            "f()*()*int"
	            ,
	            },     
/////////////////  48   ///////////////////	
	            {
	            "f(int i){}"                                                            
	            ,
	            "all"
	            ,
	            "//FunctionDefinition"
	            ,
	            "f(int)int"
	            ,
	            },
/////////////////  49   ///////////////////	
	            {
	            "f(int i,...){}"                                                        
	            ,
	            "all"
	            ,
	            "//FunctionDefinition"
	            ,
	            "f(int,...)int"
	            ,
	            },
/////////////////  50   ///////////////////	
	            {
	            "void f(int,...){}"                                                     
	            ,
	            "all"
	            ,
	            "//FunctionDefinition"
	            ,
	            "f(int,...)void"
	            ,
	            },
/////////////////  51   ///////////////////	
	            {
	            "void f(int i,void *j){}"                                               
	            ,
	            "all"
	            ,
	            "//FunctionDefinition"
	            ,
	            "f(int,*void)void"
	            ,
	            },
/////////////////  52   ///////////////////	
	            {
	            "void f(int i,double j,float i[]){}"                                    
	            ,
	            "all"
	            ,
	            "//FunctionDefinition"
	            ,
	            "f(int,double,[]float)void"
	            ,
	            },
/////////////////  53   ///////////////////	
	            {
	            "void f(int i,double j,float *i[]){}"                                   
	            ,
	            "all"
	            ,
	            "//FunctionDefinition"
	            ,
	            "f(int,double,[]*float)void"
	            ,
	            },
/////////////////  54   ///////////////////	
	            {
	            "void f(int i,double j,float (*i)[]){}"                                 
	            ,
	            "all"
	            ,
	            "//FunctionDefinition"
	            ,
	            "f(int,double,*[]float)void"
	            ,
	            },
/////////////////  55   ///////////////////	
	            {
	            "void f(int i,double j,float (*i)()){}"                                 
	            ,
	            "all"
	            ,
	            "//FunctionDefinition"
	            ,
	            "f(int,double,*()float)void"
	            ,
	            },
/////////////////  56   ///////////////////	
	            {
	            "void f(int i,double j,float (*i())()){}"                               
	            ,
	            "all"
	            ,
	            "//FunctionDefinition"
	            ,
	            "f(int,double,()*()float)void"
	            ,
	            },
/////////////////  57   ///////////////////	
	            {
	            "void f(int i,double j,float (*i)()()){}"                               
	            ,
	            "all"
	            ,
	            "//FunctionDefinition"
	            ,
	            "f(int,double,*()()float)void"
	            ,
	            },
///////////////// 58   ///////////////////	
	            {
	            "void f(int i,double j,float (*i)(int l)()){}"                          
	            ,
	            "all"
	            ,
	            "//FunctionDefinition"
	            ,
	            "f(int,double,*(int)()float)void"
	            ,
	            },
/////////////////  59   ///////////////////	
	            {
	            "void (*f)();"                                                         
	            ,
	            "all"
	            ,
	            "//Declarator"
	            ,
	            "*()void"
	            ,
	            },
/////////////////  60   ///////////////////	
	            {
	            "const int i;"                                                         
	            ,
	            "all"
	            ,
	            "//Declarator"
	            ,
	            "const int"
	            ,
	            },
///////////////// 61   ///////////////////	
	            {
	            "int const i;"                                                         
	            ,
	            "all"
	            ,
	            "//Declarator"
	            ,
	            "const int"
	            ,
	            },
/////////////////  62   ///////////////////	
	            {
	            "const const int const i;"                                             
	            ,
	            "all"
	            ,
	            "//Declarator"
	            ,
	            "const int"
	            ,
	            },
/////////////////  63   ///////////////////	
	            {
	            "const const int const const i;"                                       
	            ,
	            "all"
	            ,
	            "//Declarator"
	            ,
	            "const int"
	            ,
	            },
/////////////////  64   ///////////////////	
	            {
	            "const i;"                                                             
	            ,
	            "all"
	            ,
	            "//Declarator"
	            ,
	            "const int"
	            ,
	            },
/////////////////  65   ///////////////////	
	            {
	            "const const volatile i;"                                              
	            ,
	            "all"
	            ,
	            "//Declarator"
	            ,
	            "const volatile int"
	            ,
	            },
/////////////////  66  ///////////////////	
	            {
	            "const int  i,j;"                                                      
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='j']"
	            ,
	            "const int"
	            ,
	            },
///////////////// 67   ///////////////////	
	            {
	            "int const * i;"                                                       
	            ,
	            "all"
	            ,
	            "//Declarator"
	            ,
	            "*const int"
	            ,
	            },
/////////////////  68   ///////////////////	
	            {
	            "int const i,*j;"                                                      
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='j']"
	            ,
	            "*const int"
	            ,
	            },
/////////////////  69   ///////////////////	
	            {
	            "int *const i;"                                                        
	            ,
	            "all"
	            ,
	            "//Declarator"
	            ,
	            "const *int"
	            ,
	            },
/////////////////  70   ///////////////////	
	            {
	            "int const *const i;"                                                  
	            ,
	            "all"
	            ,
	            "//Declarator"
	            ,
	            "const *const int"
	            ,
	            },       
/////////////////  71   ///////////////////	
	            {
	            "const int const *const i;"                                            
	            ,
	            "all"
	            ,
	            "//Declarator"
	            ,
	            "const *const int"
	            ,
	            },
/////////////////  72  ///////////////////	
	            {
	            "const const *const i;"                                                
	            ,
	            "all"
	            ,
	            "//Declarator"
	            ,
	            "const *const int"
	            ,
	            },
/////////////////  73   ///////////////////	
	            {
	            "int i,* const j;"                                                     
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='j']"
	            ,
	            "const *int"
	            ,
	            },
/////////////////  74   ///////////////////	
	            {
	            "int i,* const const j;"                                               
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='j']"
	            ,
	            "const *int"
	            ,
	            }, 
/////////////////  75   ///////////////////	
	            {
	            "int i,* const *const j;"                                              
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='j']"
	            ,
	            "const *const *int"
	            ,
	            },
/////////////////  76   ///////////////////	
	            {
	            "int i,* const *const const j;"                                        
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='j']"
	            ,
	            "const *const *int"
	            ,
	            },  
/////////////////  77   ///////////////////	
	            {
	            "int i,* const *volatile const j;"                                     
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='j']"
	            ,
	            "const volatile *const *int"
	            ,
	            },
/////////////////  78   ///////////////////	
	            {
	            "void f(int i,const *volatile const j);"                               
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='j']"
	            ,
	            "const volatile *const int"
	            ,
	            },
/////////////////  79   ///////////////////	
	            {
	            "void f(int ,const int);"                                              
	            ,
	            "all"
	            ,
	            "//ParameterDeclaration[2]"
	            ,
	            "const int"
	            ,
	            },
/////////////////  80   ///////////////////	
	            {
	            "void f(int ,const int*);"                                             
	            ,
	            "all"
	            ,
	            "//ParameterDeclaration[2]"
	            ,
	            "*const int"
	            ,
	            },
/////////////////  81   ///////////////////	
	            {
	            "void f(int ,int const*);"                                             
	            ,
	            "all"
	            ,
	            "//ParameterDeclaration[2]"
	            ,
	            "*const int"
	            ,
	            },
/////////////////  82   ///////////////////	
	            {
	            "void f(int ,const*);"                                                 
	            ,
	            "all"
	            ,
	            "//ParameterDeclaration[2]"
	            ,
	            "*const int"
	            ,
	            },
/////////////////  83   ///////////////////	
	            {
	            "void f(int ,int const* const);"                                       
	            ,
	            "all"
	            ,
	            "//ParameterDeclaration[2]"
	            ,
	            "const *const int"
	            ,
	            },    
/////////////////  84   ///////////////////	
	            {
	            "void f(int ,const *volatile const );"                                 
	            ,
	            "all"
	            ,
	            "//ParameterDeclaration[2]"
	            ,
	            "const volatile *const int"
	            ,
	            },
/////////////////  85   ///////////////////	
	            {
	            "void f(int ,int const *volatile const );"                             
	            ,
	            "all"
	            ,
	            "//ParameterDeclaration[2]"
	            ,
	            "const volatile *const int"
	            ,
	            },
/////////////////  86   ///////////////////	
	            {
	            "void f(int ,int const* const*);"                                      
	            ,
	            "all"
	            ,
	            "//ParameterDeclaration[2]"
	            ,
	            "*const *const int"
	            ,
	            },
/////////////////  87   ///////////////////	
	            {
	            "void f(int ,int(*const)[]);"                                          
	            ,
	            "all"
	            ,
	            "//ParameterDeclaration[2]"
	            ,
	            "const *[]int"
	            ,
	            },
/////////////////  88   ///////////////////	
	            {
	            "void f(int ,int*const(*const)[]);"                                    
	            ,
	            "all"
	            ,
	            "//ParameterDeclaration[2]"
	            ,
	            "const *[]const *int"
	            ,
	            },
/////////////////  89   ///////////////////	
	            {
	            "void f(int ,volatile int*const(*const)[]);"                           
	            ,
	            "all"
	            ,
	            "//ParameterDeclaration[2]"
	            ,
	            "const *[]const *volatile int"
	            ,
	            },
/////////////////  90   ///////////////////	
	            {
	            "void f(int ,volatile int*const(*const)());"                           
	            ,
	            "all"
	            ,
	            "//ParameterDeclaration[2]"
	            ,
	            "const *()const *volatile int"
	            ,
	            },
/////////////////  91   ///////////////////	
	            {
	            "void f(int ,volatile int*const(*const)(int));"                        
	            ,
	            "all"
	            ,
	            "//ParameterDeclaration[2]"
	            ,
	            "const *(int)const *volatile int"
	            ,
	            },
/////////////////  92   ///////////////////	
	            {
	            "int f(i);"                                                            
	            ,
	            "keil"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int)int"
	            ,
	            },
/////////////////  93   ///////////////////	
	            {
	            "int f(int i,j);"                                                      
	            ,
	            "keil"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f(int,int)int"
	            ,
	            },
/////////////////  94   ///////////////////	
	            {
	            "int f(void);"                                                         
	            ,
	            "all"
	            ,
	            "//FunctionDeclaration"
	            ,
	            "f()int"
	            ,
	            },
/////////////////  95   ///////////////////	
	            {
	            "int f(int j,i);"                                                      
	            ,
	            "keil"
	            ,
	            "//ParameterDeclaration[2]"
	            ,
	            "int"
	            ,
	            },
/////////////////  96   ///////////////////	
	            {
	            "void f(i)"                                                            +"\n"+
	            "int i;"                                                               +"\n"+
	            "{"                                                                    +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//FunctionDefinition"
	            ,
	            "f(int)void"
	            ,
	            },
/////////////////  97   ///////////////////	
	            {
	            "void f(i,j)"                                                          +"\n"+
	            "int i;"                                                               +"\n"+
	            "int j;"                                                               +"\n"+
	            "{"                                                                    +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//FunctionDefinition"
	            ,
	            "f(int,int)void"
	            ,
	            },
/////////////////  98   ///////////////////	
	            {
	            "void f(i,j)"                                                          +"\n"+
	            "double i;"                                                            +"\n"+
	            "int j;"                                                               +"\n"+
	            "{"                                                                    +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//FunctionDefinition"
	            ,
	            "f(double,int)void"
	            ,
	            },
/////////////////  99   ///////////////////	
	            {
	            "void f(j,i)"                                                          +"\n"+
	            "double i;"                                                            +"\n"+
	            "int j;"                                                               +"\n"+
	            "{"                                                                    +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//FunctionDefinition"
	            ,
	            "f(int,double)void"
	            ,
	            },
/////////////////  100   ///////////////////	
	            {
	            "void f(i,j,k,l)"                                                      +"\n"+
	            "double i,l;"                                                          +"\n"+
	            "int j,k;"                                                             +"\n"+
	            "{"                                                                    +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//FunctionDefinition"
	            ,
	            "f(double,int,int,double)void"
	            ,
	            },
/////////////////  101   ///////////////////	
	            {
	            "typedef int mint;"                                                    +"\n"+
	            "mint i;"                                                              
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='i']"
	            ,
	            "mint:int"
	            ,
	            },
/////////////////  102   ///////////////////	
	            {
	            "typedef int* mint;"                                                   +"\n"+
	            "mint i;"                                                              
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='i']"
	            ,
	            "mint:*int"
	            ,
	            },
/////////////////  103   ///////////////////	
	            {
	            "typedef int mint[];"                                                  +"\n"+
	            "mint i;"                                                              
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='i']"
	            ,
	            "mint:[]int"
	            ,
	            },
/////////////////  104   ///////////////////	
	            {
	            "typedef int mint[10][10];"                                            +"\n"+
	            "mint i;"                                                              
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='i']"
	            ,
	            "mint:[10][10]int"
	            ,
	            },  
/////////////////  105   ///////////////////	
	            {
	            "typedef const int mint[10][10];"                                      +"\n"+
	            "mint i;"                                                              
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='i']"
	            ,
	            "mint:[10][10]const int"
	            ,
	            },
/////////////////  106   ///////////////////	
	            {
	            "typedef int mint(int);"                                               +"\n"+
	            "mint i;"                                                              
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='i']"
	            ,
	            "mint:(int)int"
	            ,
	            },
/////////////////  107   ///////////////////	
	            {
	            "typedef void (*mint)(int);"                                           +"\n"+
	            "mint i;"                                                              
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='i']"
	            ,
	            "mint:*(int)void"
	            ,
	            },
/////////////////  108   ///////////////////	
	            {
	            "struct sss{int i;}a;"                                                 
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='a']"
	            ,
	            "struct sss"
	            ,
	            },
/////////////////  109   ///////////////////	
	            {
	            "union sss{int i;}a;"                                                  
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='a']"
	            ,
	            "union sss"
	            ,
	            },
/////////////////  110   ///////////////////	
	            {
	            "union {int i;}a;"                                                     
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='a']"
	            ,
	            "union NoName_0"
	            ,
	            },
/////////////////  111   ///////////////////	
	            {
	            "struct {int i;}a;"                                                    
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='a']"
	            ,
	            "struct NoName_0"
	            ,
	            },
/////////////////  112   ///////////////////	
	            {
	            "struct ss{int i;}a,b;"                                                
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='a']"
	            ,
	            "struct ss"
	            ,
	            },
/////////////////  113   ///////////////////	
	            {
	            "struct ss{int i;}a,*b;"                                               
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='b']"
	            ,
	            "*struct ss"
	            ,
	            },
/////////////////  114   ///////////////////	
	            {
	            "struct ss{int i;}a,*b[];"                                             
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='b']"
	            ,
	            "[]*struct ss"
	            ,
	            },
/////////////////  115   ///////////////////	
	            {
	            "enum ee{a,b,c}i;"                                                     
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='i']"
	            ,
	            "enum ee"
	            ,
	            },
/////////////////  116   ///////////////////	
	            {
	            "enum {a,b,c}i;"                                                       
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='i']"
	            ,
	            "enum NoName_0"
	            ,
	            },
/////////////////  117   ///////////////////	
	            {
	            "typedef struct sss{int i;}a;"                                         +"\n"+
	            "a i;"                                                                 
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='i']"
	            ,
	            "a:struct sss"
	            ,
	            },
/////////////////  118   ///////////////////	
	            {
	            "typedef struct sss{int i;}a;"                                         +"\n"+
	            "void f(){"                                                            +"\n"+
	            "	a i;"                                                                +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='i']"
	            ,
	            "a:struct sss"
	            ,
	            },
/////////////////  119   ///////////////////	
	            {
	            "typedef struct sss{int i;}a;"                                         
	            ,
	            "all"
	            ,
	            "//StructDeclarator"
	            ,
	            "int"
	            ,
	            },
/////////////////  120   ///////////////////	
	            {
	            "struct ss{ "                                                          +"\n"+
	            "int i;"                                                               +"\n"+
	            "};"                                                                   +"\n"+
	            ""                                                                     +"\n"+
	            "struct ss a;"                                                         
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='a']"
	            ,
	            "struct ss"
	            ,
	            },
/////////////////  121   ///////////////////	
	            {
	            "enum e{i};"                                                           +"\n"+
	            "enum e a;"                                                            
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='a']"
	            ,
	            "enum e"
	            ,
	            },
/////////////////  122   ///////////////////	
	            {
	            "fun(int i){int f(int i){}}"                                           
	            ,
	            "gcc"
	            ,
	            "//NestedFunctionDefinition[@Image='f']"
	            ,
	            "f(int)int"
	            ,
	            },
/////////////////  123   ///////////////////	
	            {
	            "fun(int i){auto int f(int i);}"                                       
	            ,
	            "gcc"
	            ,
	            "//NestedFunctionDeclaration[@Image='f']"
	            ,
	            "f(int)int"
	            ,
	            },
/////////////////  124   ///////////////////	
	            {
	            "char fun()"                                                           +"\n"+
	            "{"                                                                    +"\n"+
	            "	auto f(double d);"                                                   +"\n"+
	            "	int f(double d){return 0;}"                                          +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "//NestedFunctionDeclaration[@Image='f']"
	            ,
	            "f(double)int"
	            ,
	            },
/////////////////  125   ///////////////////	
	            {
	            "char fun()"                                                           +"\n"+
	            "{"                                                                    +"\n"+
	            "	auto int f();"                                                       +"\n"+
	            "	int f(double d){return 0;}"                                          +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "//NestedFunctionDeclaration[@Image='f']"
	            ,
	            "f()int"
	            ,
	            },
/////////////////  126   ///////////////////	
	            {
	            "char fun()"                                                           +"\n"+
	            "{"                                                                    +"\n"+
	            "	auto f();"                                                           +"\n"+
	            "	int f(double d){return 0;}"                                          +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "//NestedFunctionDeclaration[@Image='f']"
	            ,
	            "f()int"
	            ,
	            },
/////////////////  127   ///////////////////	
	            {
	            "char fun()"                                                           +"\n"+
	            "{"                                                                    +"\n"+
	            "	auto int (f)();"                                                     +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "//NestedFunctionDeclaration"
	            ,
	            "f()int"
	            ,
	            },
/////////////////  128   ///////////////////	
	            {
	            "f()"                                                                  +"\n"+
	            "{"                                                                    +"\n"+
	            "	int i;"                                                              +"\n"+
	            "	for(i=0;i<10;i++)"                                                   +"\n"+
	            "	{"                                                                   +"\n"+
	            "		int j;"                                                             +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='j']"
	            ,
	            "int"
	            ,
	            },
/////////////////  129   ///////////////////	
	            {
	            "char j=(char)i;"                                                      
	            ,
	            "all"
	            ,
	            "//TypeName"
	            ,
	            "char"
	            ,
	            },
/////////////////  130   ///////////////////	
	            {
	            "f()"                                                                  +"\n"+
	            "{"                                                                    +"\n"+
	            "	if(1)"                                                               +"\n"+
	            "	{"                                                                   +"\n"+
	            "		int j;"                                                             +"\n"+
	            "		return;"                                                            +"\n"+
	            "	}"                                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "//Declarator[@Image='j']"
	            ,
	            "int"
	            ,
	            },
/////////////////  131   ///////////////////	
	            {
	            "f()"                                                                  +"\n"+
	            "{"                                                                    +"\n"+
	            "	float ff(){}"                                                        +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "//NestedFunctionDefinition"
	            ,
	            "ff()float"
	            ,
	            },
/////////////////  132   ///////////////////	
	            {
	            "char fun()"                                                           +"\n"+
	            "{"                                                                    +"\n"+
	            "	int f(i,j)"                                                          +"\n"+
	            "	char i;"                                                             +"\n"+
	            "	int j;"                                                              +"\n"+
	            "	{}"                                                                  +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "//NestedFunctionDefinition"
	            ,
	            "f(char,int)int"
	            ,
	            },
/////////////////  133   ///////////////////	
	            {
	            "int *p;"                                                              +"\n"+
	            "unsigned int *i=(unsigned int*)p;"                                    
	            ,
	            "all"
	            ,
	            "//TypeName"
	            ,
	            "*unsigned int"
	            ,
	            },
/////////////////  134   ///////////////////	
	            {
	            "typeof(int) a=1;"                                                     
	            ,
	            "gcc"
	            ,
	            "//TypeSpecifier"
	            ,
	            "int"
	            ,
	            },
/////////////////  135   ///////////////////	
	            {
	            "struct s{"                                                            +"\n"+
	            "int i:1;"                                                             +"\n"+
	            "char c:2;"                                                            +"\n"+
	            "};"                                                                   
	            ,
	            "all"
	            ,
	            "//StructDeclarator"
	            ,
	            "int:bitfield_1"
	            ,
	            },
/////////////////  136   ///////////////////	
	            {
	            "struct s{struct s *ss;int i;}*ptr;"                                   +"\n"+
	            "struct s* ps=(const struct s*)ptr->ss;"                               
	            ,
	            "all"
	            ,
	            "//TypeName"
	            ,
	            "*const struct s"
	            ,
	            },
/////////////////  137   ///////////////////	
	            {
	            "void test(){"                                                         +"\n"+
	            "	typeof (typeof (char *)[4]) yyy={\"abc\",\"232ad\",\"sdfsad\",\"sdf\"};"     +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "//DeclarationSpecifiers[@BeginLine='2']"
	            ,
	            "[4]*char"
	            ,
	            },
/////////////////  138   ///////////////////	
	            {
	            "typeof(int*) i;"                                                      +"\n"+
	            "struct s{int i;};"                                                    
	            ,
	            "gcc"
	            ,
	            "//Declarator[@Image='i']"
	            ,
	            "*int"
	            ,
	            },
/////////////////  139  ///////////////////	
	            {
	            "char data var1;"                                                      
	            ,
	            "keil"
	            ,
	            "//Declarator"
	            ,
	            "data char"
	            ,
	            },
/////////////////  140   ///////////////////	
	            {
	            "char code text[] = \"ENTER PARAMETER:\";"                               
	            ,
	            "keil"
	            ,
	            "//Declarator"
	            ,
	            "[]code char"
	            ,
	            },
/////////////////  141   ///////////////////	
	            {
	            "unsigned long xdata array[100];"                                      
	            ,
	            "keil"
	            ,
	            "//Declarator"
	            ,
	            "[100]xdata unsigned long"
	            ,
	            },
/////////////////  142   ///////////////////	
	            {
	            "float idata x;"                                                       
	            ,
	            "keil"
	            ,
	            "//Declarator"
	            ,
	            "idata float"
	            ,
	            },
/////////////////  143  ///////////////////	
	            {
	            "unsigned int pdata dimension;"                                        
	            ,
	            "keil"
	            ,
	            "//Declarator"
	            ,
	            "pdata unsigned int"
	            ,
	            },
/////////////////  144   ///////////////////	
	            {
	            "unsigned char xdata vector[10][4][4];"                                
	            ,
	            "keil"
	            ,
	            "//Declarator"
	            ,
	            "[10][4][4]xdata unsigned char"
	            ,
	            },
/////////////////  145   ///////////////////	
	            {
	            "char bdata flags;"                                                    
	            ,
	            "keil"
	            ,
	            "//Declarator"
	            ,
	            "bdata char"
	            ,
	            },
/////////////////  146   ///////////////////	
	            {
	            "bit testfunc(bit flag1,bit flag2)"                                    +"\n"+
	            "{"                                                                    +"\n"+
	            "	return 0;"                                                           +"\n"+
	            "}"                                                                    
	            ,
	            "keil"
	            ,
	            "//Declarator[@BeginColumn='5']"
	            ,
	            "testfunc(bit,bit)bit"
	            ,
	            },
/////////////////  147   ///////////////////	
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
/////////////////  148   ///////////////////	
	            {
	            "void (f)(){}"                                                         
	            ,
	            "all"
	            ,
	            "//Declarator[@BeginColumn='6']"
	            ,
	            "f()void"
	            ,
	            },


        }
		);
	}
}
