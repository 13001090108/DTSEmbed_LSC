package softtest.test.c.symboltable;

import static org.junit.Assert.*;

import java.io.*;
import java.util.*;

import softtest.ast.c.*;
import softtest.symboltable.c.*;
import softtest.tools.c.jaxen.*;

import org.junit.*;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
/**
 * 
 * @author zys
 * 回归测试：测试复杂程序段的作用域及其下的变量声明是否正确
 */
@RunWith(Parameterized.class)
public class TestNameDeclarationAndScope {
	private String source = null;
	private String compiletype=null;
	private String type = null;
	
	public TestNameDeclarationAndScope(String source,String compiletype, String type) {
		this.source = source;
		this.compiletype=compiletype;
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
		
		assertEquals("Scope Error!",type,
				((AbstractScope)astroot.getScope()).print());
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
	            "int i;"                                                               +"\n"+
	            "f(int k){"                                                            +"\n"+
	            "int j;"                                                               +"\n"+
	            "return j;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "SourceFileScope (null): (methods: f < f(int)int >)(variables: i < int >)"+"\n"+
	"  MethodScope(null): (variables: k < int >)"+"\n"+
	"    LocalScope: (variables: j < int >)"+"\n"
	            ,
	            },
/////////////////  1   ///////////////////	
	            {
	            "int i;"                                                               +"\n"+
	            "f(int k){"                                                            +"\n"+
	            "int j;"                                                               +"\n"+
	            "int ff(int i)"                                                        +"\n"+
	            "{"                                                                    +"\n"+
	            "	int j,k,h;"                                                          +"\n"+
	            "}"                                                                    +"\n"+
	            "return j;"                                                            +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "SourceFileScope (null): (methods: f < f(int)int >)(variables: i < int >)"+"\n"+
	"  MethodScope(null): (variables: k < int >)"+"\n"+
	"    LocalScope: (variables: j < int >)"+"\n"+
	"      MethodScope(null): (variables: i < int >)"+"\n"+
	"        LocalScope: (variables: j < int >,k < int >,h < int >)"+"\n"
	            ,
	            },
/////////////////  2   ///////////////////	
	            {
	            "f(){"                                                                 +"\n"+
	            "int i;"                                                               +"\n"+
	            "auto int ff(char c);"                                                 +"\n"+
	            "int j;"                                                               +"\n"+
	            "int ff(char c){"                                                      +"\n"+
	            "float f;"                                                             +"\n"+
	            "}"                                                                    +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "SourceFileScope (null): (methods: f < f()int >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: j < int >,i < int >)"+"\n"+
	"      MethodScope(null): (variables: c < char >)"+"\n"+
	"      MethodScope(null): (variables: c < char >)"+"\n"+
	"        LocalScope: (variables: f < float >)"+"\n"
	            ,
	            },
/////////////////  3 for-01   ///////////////////	
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
	            "SourceFileScope (null): (methods: main < main()int >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: a < int >,i < int >)"+"\n"+
	"      LocalScope: "+"\n"+
	"        LocalScope: "+"\n"
	            ,
	            },
/////////////////  4 for-02   ///////////////////	
	            {
	            "void main() {"                                                        +"\n"+
	            "int i;"                                                               +"\n"+
	            "int a = 1;"                                                           +"\n"+
	            "for(i=6;i>=0;i--)"                                                    +"\n"+
	            "{"                                                                    +"\n"+
	            "if (i>a) continue;"                                                   +"\n"+
	            "else break;"                                                          +"\n"+
	            "}"                                                                    +"\n"+
	            "return;"                                                              +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "SourceFileScope (null): (methods: main < main()void >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: a < int >,i < int >)"+"\n"+
	"      LocalScope: "+"\n"+
	"        LocalScope: "+"\n"+
	"          LocalScope: "+"\n"
	            ,
	            },
/////////////////  5 for-03   ///////////////////	
	            {
	            "#include<stdio.h>"                                                    +"\n"+
	            ""                                                                     +"\n"+
	            "main() {"                                                             +"\n"+
	            "int i;"                                                               +"\n"+
	            "int a;"                                                               +"\n"+
	            "for(i=0;i<6;i++)"                                                     +"\n"+
	            "{goto e1;}"                                                           +"\n"+
	            "a=2; "                                                                +"\n"+
	            "e1:"                                                                  +"\n"+
	            "i=10;"                                                                +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "SourceFileScope (null): (methods: main < main()int >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: a < int >,i < int >)"+"\n"+
	"      LocalScope: "+"\n"+
	"        LocalScope: "+"\n"
	            ,
	            },
/////////////////  6 for-04   ///////////////////	
	            {
	            "void main()"                                                          +"\n"+
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
	            "			int testfor;"                                                      +"\n"+
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
	            "SourceFileScope (null): (methods: main < main()void >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: b < int >,c < int >,a < int >,i < int >)"+"\n"+
	"      LocalScope: "+"\n"+
	"        LocalScope: "+"\n"+
	"          LocalScope: "+"\n"+
	"            LocalScope: (variables: testfor < int >)"+"\n"+
	"              LocalScope: "+"\n"+
	"                LocalScope: "+"\n"+
	"                LocalScope: "+"\n"+
	"        LocalScope: "+"\n"
	            ,
	            },
/////////////////  7 for-05   ///////////////////	
	            {
	            "void main()"                                                          +"\n"+
	            "{"                                                                    +"\n"+
	            "int i;"                                                               +"\n"+
	            "int a=1;"                                                             +"\n"+
	            "int b=5;"                                                             +"\n"+
	            "int c=1;"                                                             +"\n"+
	            "e2:"                                                                  +"\n"+
	            "if(true)"                                                             +"\n"+
	            "{"                                                                    +"\n"+
	            "	for (i=0;i<10;i++)"                                                  +"\n"+
	            "		for(i=0;i<6;i++)"                                                   +"\n"+
	            "		{"                                                                  +"\n"+
	            "			int testfor2;"                                                     +"\n"+
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
	            "SourceFileScope (null): (methods: main < main()void >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: b < int >,c < int >,a < int >,i < int >)"+"\n"+
	"      LocalScope: "+"\n"+
	"        LocalScope: "+"\n"+
	"          LocalScope: "+"\n"+
	"            LocalScope: "+"\n"+
	"              LocalScope: (variables: testfor2 < int >)"+"\n"+
	"                LocalScope: "+"\n"+
	"                  LocalScope: "+"\n"+
	"                  LocalScope: "+"\n"+
	"        LocalScope: "+"\n"
	            ,
	            },
/////////////////  8 jum-01  ///////////////////	
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
	            "SourceFileScope (null): (methods: main < main()int >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: count < int >)"+"\n"+
	"      LocalScope: "+"\n"+
	"        LocalScope: "+"\n"
	            ,
	            },	            
/////////////////  9 jum-02   ///////////////////	
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
	            "SourceFileScope (null): (methods: main < main()int >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: count < int >)"+"\n"+
	"      LocalScope: "+"\n"+
	"        LocalScope: "+"\n"
	            ,
	            },	            
/////////////////  10 jum-03   ///////////////////	
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
	            "SourceFileScope (null): (methods: main < main()int >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: count < int >)"+"\n"+
	"      LocalScope: "+"\n"+
	"        LocalScope: "+"\n"
	            ,
	            },       
/////////////////  11  decl-01  ///////////////////	
	            {
	            "main() {"                                                             +"\n"+
	            "int count = 1;"                                                       +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "SourceFileScope (null): (methods: main < main()int >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: count < int >)"+"\n"
	            ,
	            },	            
/////////////////  12 decl-02   ///////////////////	
	            {
	            "main() {"                                                             +"\n"+
	            "int count = 1;"                                                       +"\n"+
	            "float f =0.1;"                                                        +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "SourceFileScope (null): (methods: main < main()int >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: f < float >,count < int >)"+"\n"
	            ,
	            },	            
/////////////////  13 decl-03   ///////////////////	
	            {
	            "main() {"                                                             +"\n"+
	            "int count = 1;"                                                       +"\n"+
	            "float f =0.1;"                                                        +"\n"+
	            "char c = 'A';"                                                        +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "SourceFileScope (null): (methods: main < main()int >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: f < float >,count < int >,c < char >)"+"\n"
	            ,
	            },	            
/////////////////  14 func-01   ///////////////////	
	            {
	            "main() {"                                                             +"\n"+
	            "int count = 1;"                                                       +"\n"+
	            "float f =0.1;"                                                        +"\n"+
	            "char c = 'A';"                                                        +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "SourceFileScope (null): (methods: main < main()int >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: f < float >,count < int >,c < char >)"+"\n"
	            ,
	            },	  
/////////////////  15 func-02   ///////////////////	
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
	            "SourceFileScope (null): (methods: main < main()int >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: count < int >)"+"\n"+
	"      LocalScope: "+"\n"+
	"        LocalScope: "+"\n"
	            ,
	            },
/////////////////  16 switch-01   ///////////////////	
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
	            "SourceFileScope (null): (methods: main < main()int >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: b < int >,a < int >)"+"\n"+
	"      LocalScope: "+"\n"+
	"        LocalScope: "+"\n"
	            ,
	            },
	/////////////////  17 switch-02   ///////////////////	
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
	            "SourceFileScope (null): (methods: main < main()int >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: b < int >,a < int >)"+"\n"+
	"      LocalScope: "+"\n"+
	"        LocalScope: "+"\n"+
	"      LocalScope: "+"\n"+
	"        LocalScope: "+"\n"
	            ,
	            },
	/////////////////  18 switch-03   ///////////////////	
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
	            "SourceFileScope (null): (methods: main < main()int >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: b < int >,a < int >)"+"\n"+
	"      LocalScope: "+"\n"+
	"        LocalScope: "+"\n"+
	"          LocalScope: "+"\n"+
	"            LocalScope: "+"\n"
	            ,
	            },
/////////////////  19   ///////////////////	
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
	            "SourceFileScope (null): (methods: main < main()int >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: b < int >,a < int >)"+"\n"+
	"      LocalScope: "+"\n"+
	"        LocalScope: "+"\n"+
	"          LocalScope: "+"\n"+
	"            LocalScope: "+"\n"
	            ,
	            },
	/////////////////  20 switch-05   ///////////////////	
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
	            "SourceFileScope (null): (methods: main < main()int >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: b < int >,a < int >,grade < int >)"+"\n"+
	"      LocalScope: "+"\n"+
	"        LocalScope: "+"\n"+
	"          LocalScope: "+"\n"
	            ,
	            },
	/////////////////  21 switch-06   ///////////////////	
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
	            "SourceFileScope (null): (methods: main < main()int >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: b < int >,a < int >,grade < int >,i < int >)"+"\n"+
	"      LocalScope: "+"\n"+
	"        LocalScope: "+"\n"+
	"          LocalScope: "+"\n"+
	"            LocalScope: "+"\n"+
	"              LocalScope: "+"\n"
	            ,
	            },
	/////////////////  22 switch-07   ///////////////////	
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
	            "SourceFileScope (null): (methods: main < main()int >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: b < int >,counter < int >,a < int >,grade < int >,i < int >)"+"\n"+
	"      LocalScope: "+"\n"+
	"        LocalScope: "+"\n"+
	"          LocalScope: "+"\n"+
	"            LocalScope: "+"\n"+
	"              LocalScope: "+"\n"+
	"                LocalScope: "+"\n"+
	"                  LocalScope: "+"\n"+
	"                    LocalScope: "+"\n"
	            ,
	            },
	/////////////////  23 switch-08   ///////////////////	
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
	            "SourceFileScope (null): (methods: main < main()int >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: b < int >,c < int >,counter < int >,a < int >,grade < int >,i < int >)"+"\n"+
	"      LocalScope: "+"\n"+
	"        LocalScope: "+"\n"+
	"          LocalScope: "+"\n"+
	"            LocalScope: "+"\n"+
	"              LocalScope: "+"\n"+
	"                LocalScope: "+"\n"+
	"                  LocalScope: "+"\n"+
	"                    LocalScope: "+"\n"
	            ,
	            },
/////////////////  24 s-testreport-1   ///////////////////	
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
	            "SourceFileScope (null): (methods: add < add(float,float)float >)"+"\n"+
	"  MethodScope(null): (variables: y < float >,x < float >)"+"\n"+
	"    LocalScope: (variables: z < float >)"+"\n"
	            ,
	            },

	/////////////////  25 s-testreport-2   ///////////////////	
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
	            "SourceFileScope (null): (methods: main < main()void >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: count < int >)"+"\n"+
	"      LocalScope: "+"\n"+
	"        LocalScope: "+"\n"+
	"          LocalScope: "+"\n"+
	"          LocalScope: "+"\n"
	            ,
	            },


	/////////////////  26 s-testreport-3   ///////////////////	
	            {
	            "void main() {"                                                        +"\n"+
	            " int i=10;"                                                           +"\n"+
	            " label1: do{"                                                         +"\n"+
	            "	int test1;"                                                          +"\n"+
	            "   if(i>10)"                                                          +"\n"+
	            "     {continue; int testIf;}"                                         +"\n"+
	            "   else "                                                             +"\n"+
	            "     {"                                                               +"\n"+
	            "	 int testElse;"                                                      +"\n"+
	            "	 if(i<10)"                                                           +"\n"+
	            "       {break; int testif2;}"                                         +"\n"+
	            "     else"                                                            +"\n"+
	            "       {i++; int testelse2;}"                                         +"\n"+
	            "	}"                                                                   +"\n"+
	            "	}"                                                                   +"\n"+
	            "  while(i<=20);"                                                      +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "SourceFileScope (null): (methods: main < main()void >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: i < int >)"+"\n"+
	"      LocalScope: "+"\n"+
	"        LocalScope: (variables: test1 < int >)"+"\n"+
	"          LocalScope: "+"\n"+
	"            LocalScope: (variables: testIf < int >)"+"\n"+
	"            LocalScope: (variables: testElse < int >)"+"\n"+
	"              LocalScope: "+"\n"+
	"                LocalScope: (variables: testif2 < int >)"+"\n"+
	"                LocalScope: (variables: testelse2 < int >)"+"\n"
	            ,
	            },


	/////////////////  27 s-testreport-4   ///////////////////	
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
	            "SourceFileScope (null): (methods: add < add(float,float)float >,main < main()int >)"+"\n"+
	"  MethodScope(null): (variables: y < float >,x < float >)"+"\n"+
	"    LocalScope: (variables: z < float >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: count < int >,count2 < float >,count3 < int >)"+"\n"+
	"      LocalScope: "+"\n"+
	"        LocalScope: "+"\n"+
	"          LocalScope: "+"\n"+
	"          LocalScope: "+"\n"+
	"      LocalScope: "+"\n"+
	"        LocalScope: "+"\n"+
	"          LocalScope: "+"\n"+
	"            LocalScope: "+"\n"+
	"            LocalScope: "+"\n"
	            ,
	            },

	/////////////////  28 s-testreport-5   ///////////////////	
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
	            "SourceFileScope (null): (methods: main < main()void >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: sum < int >,j < int >,i < int >)"+"\n"+
	"      LocalScope: "+"\n"+
	"        LocalScope: "+"\n"+
	"          LocalScope: "+"\n"+
	"            LocalScope: "+"\n"+
	"              LocalScope: "+"\n"+
	"          LocalScope: "+"\n"+
	"      LocalScope: "+"\n"+
	"      LocalScope: "+"\n"
	            ,
	            },


	/////////////////  29 s-testreport-6   ///////////////////	
	            {
	            "void main()"                                                          +"\n"+
	            "{"                                                                    +"\n"+
	            "  int i,j,sum=0;"                                                     +"\n"+
	            "  i=1;"                                                               +"\n"+
	            "label1:"                                                              +"\n"+
	            "  do{"                                                                +"\n"+
	            "	 int dowhile1;"                                                      +"\n"+
	            "     sum=sum+i;"                                                      +"\n"+
	            "     i++;"                                                            +"\n"+
	            "        do{"                                                          +"\n"+
	            "			int dowhile2;"                                                     +"\n"+
	            "            if(i==10)"                                                +"\n"+
	            "               {continue;int testif1;}"                               +"\n"+
	            "            else {break; int testelse1;}"                             +"\n"+
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
	            "gcc"
	            ,
	            "SourceFileScope (null): (methods: main < main()void >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: sum < int >,j < int >,i < int >)"+"\n"+
	"      LocalScope: "+"\n"+
	"        LocalScope: (variables: dowhile1 < int >)"+"\n"+
	"          LocalScope: "+"\n"+
	"            LocalScope: (variables: dowhile2 < int >)"+"\n"+
	"              LocalScope: "+"\n"+
	"                LocalScope: (variables: testif1 < int >)"+"\n"+
	"                LocalScope: (variables: testelse1 < int >)"+"\n"+
	"          LocalScope: "+"\n"+
	"      LocalScope: "+"\n"+
	"      LocalScope: "+"\n"
	            ,
	            },

	///////////////// 30 s-testreport-7   ///////////////////	
	{
	            "void main()"                                                          +"\n"+
	            "{"                                                                    +"\n"+
	            "	int sum;"                                                            +"\n"+
	            "	int i;"                                                              +"\n"+
	            "i+1;"                                                                 +"\n"+
	            "    if(j==0)"                                                         +"\n"+
	            "      int testif;"                                                    +"\n"+
	            "    else"                                                             +"\n"+
	            "      int testelse;"                                                  +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "SourceFileScope (null): (methods: main < main()void >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: sum < int >,i < int >)"+"\n"+
	"      LocalScope: (variables: testif < int >,testelse < int >)"+"\n"
	            ,
	            },

	///////////////// 31 s-testreport-8   ///////////////////	
	            {
	            "void main()"                                                          +"\n"+
	            "{"                                                                    +"\n"+
	            "	int sum;"                                                            +"\n"+
	            "	int i;"                                                              +"\n"+
	            "i+1;"                                                                 +"\n"+
	            "    if(j==0)"                                                         +"\n"+
	            "      {int testif;}"                                                  +"\n"+
	            "    else"                                                             +"\n"+
	            "      {int testelse;}"                                                +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "SourceFileScope (null): (methods: main < main()void >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: sum < int >,i < int >)"+"\n"+
	"      LocalScope: "+"\n"+
	"        LocalScope: (variables: testif < int >)"+"\n"+
	"        LocalScope: (variables: testelse < int >)"+"\n"
	            ,
	            },
/////////////////  32   ///////////////////	
	            {
	            "union ss{int i;}s1;"                                                  +"\n"+
	            "union ss s2;"                                                         +"\n"+
	            "int i;"                                                               +"\n"+
	            "char f(){"                                                            +"\n"+
	            "int i;"                                                               +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "SourceFileScope (null): (classes: ss < union ss >)(methods: f < f()char >)(variables: s2 < union ss >,s1 < union ss >,i < int >)"+"\n"+
	"  ClassScope (ss): (variables: i < int >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: i < int >)"+"\n"
	            ,
	            },
/////////////////  33   ///////////////////	
	            {
	            "enum ss{i,j,k=3,}s1;"                                                 +"\n"+
	            "enum ss s2;"                                                          +"\n"+
	            "int i;"                                                               +"\n"+
	            "char f(){"                                                            +"\n"+
	            "int i;"                                                               +"\n"+
	            "}"                                                                    
	            ,
	            "all"
	            ,
	            "SourceFileScope (null): (classes: ss < enum ss >)(methods: f < f()char >)(variables: s2 < enum ss >,s1 < enum ss >,j < int >,k < int >,i < int >,i < int >)"+"\n"+
	"  ClassScope (ss): "+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: i < int >)"+"\n"
	            ,
	            },
/////////////////  34  ///////////////////	
	            {
	            "double ff();"                                                         +"\n"+
	            "typedef char * string;"                                               +"\n"+
	            "char f(int []){"                                                      +"\n"+
	            "typeof(string) str=\"abc\";"                                            +"\n"+
	            "int *i;"                                                              +"\n"+
	            "auto float nestFunc(int j,int k);"                                    +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "SourceFileScope (null): (classes: string < string:*char >)(methods: f < f([]int)char >,ff < ff()double >)"+"\n"+
	"  MethodScope(null): "+"\n"+
	"    LocalScope: (variables: str < string:*char >,i < *int >)"+"\n"+
	"      MethodScope(null): (variables: j < int >,k < int >)"+"\n"
	            ,
	            },


	            
	            
	            
	            
	            
	            
	            
	            
        });
	}
}
