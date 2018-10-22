package softtest.test.gcc.rules.fault;

import java.util.Arrays;
import java.util.Collection;
import java.util.Set;

import org.junit.BeforeClass;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import softtest.fsm.c.FSMLoader;
import softtest.fsm.c.FSMMachine;
import softtest.fsmanalysis.c.FSMAnalysisVisitor;
import softtest.interpro.c.InterContext;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.test.c.rules.ModelTestBase;

@RunWith(Parameterized.class)
public class Test_NPD_EXP extends ModelTestBase {
	public Test_NPD_EXP(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/NPD_EXP-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("fault");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
		
		//加载库函数摘要
		LIB_SUMMARYS_PATH="gcc_lib/npd_summary.xml";
		libManager.loadSingleLibFile(LIB_SUMMARYS_PATH);
		Set<MethodNameDeclaration> libDecls = libManager.compileLib(pre.getLibIncludes());
		interContext = InterContext.getInstance();
		interContext.addLibMethodDecl(libDecls);
	}
	
	 @Parameters
	 public static Collection<Object[]> testcaseAndResults()
	 {
		 return Arrays.asList(new Object[][] {
	/////////////////  0   ///////////////////	
		            {
		            "void f0(){"                                                            +"\n"+
		            "   int **p,a;"                                                        +"\n"+
		            "   p=323445; "                                                        +"\n"+
		            "   *p=malloc(100);"                                                   +"\n"+
		            "   a=**p;"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            ,
		            },
	///////////////// 1   ///////////////////	
		            {
		            "typedef struct {"                                                     +"\n"+
		            "   int *p;"                                                           +"\n"+
		            "}st ;"                                                                +"\n"+
		            "void f1(st *s ){"                                                      +"\n"+
		            "   int a;"                                                            +"\n"+
		            "   s->p=malloc(10);"                                                  +"\n"+
		            "   a=*(s->p);"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            ,
		            },

	/////////////////  2   ///////////////////	
		            {
		            "void f2(int **p){"                                                     +"\n"+
		            "   int  a;"                                                           +"\n"+
		            "   if(!*p)"                                                           +"\n"+
		            "a=0;"                                                                 +"\n"+
		            "   **p=1; "                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            ,
		            },
	/////////////////  3   ///////////////////	
		            {
		            "typedef struct {"                                                     +"\n"+
		            "   int *p;"                                                           +"\n"+
		            "}st ;"                                                                +"\n"+
		            "void f3(st *s ){"                                                      +"\n"+
		            "   int a;"                                                            +"\n"+
		            "   if(!s->p)"                                                         +"\n"+
		            "     a=0;"                                                            +"\n"+
		            "   a=*(s->p);"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            ,
		            },

	
	/////////////////  4  ///////////////////	
		            {
		            "void f4(int **p,int a){"                                               +"\n"+
		            "   "                                                                  +"\n"+
		            "   if((a==1)&&!*p)"                                                   +"\n"+
		            "a=0;"                                                                 +"\n"+
		            "   **p=1; "                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            ,
		            },
	///////////////// 5   ///////////////////	
		            {
		            "typedef struct {"                                                     +"\n"+
		            "   int *p;"                                                            +"\n"+
		            "}st ;"                                                                +"\n"+
		            "void f5(st *s,int a ){"                                                +"\n"+
		            "   "                                                                  +"\n"+
		            "   if((a==1)||(!s->p))"                                               +"\n"+
		            "     a=0;"                                                            +"\n"+
		            "   a=*(s->p);"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            ,
		            },
	/////////////////  6  ///////////////////	
		         
		            {
			            "struct state"                                                         +"\n"+
			            "{"                                                                    +"\n"+
			            "  struct state* next;"                                                +"\n"+
			            "  int num;"                                                           +"\n"+
			            "  int** ptr;"                                                         +"\n"+
			            "  struct nest nested;"                                                +"\n"+
			            "};"                                                                   +"\n"+
			            ""                                                                     +"\n"+
			            ""                                                                     +"\n"+
		            "void f6(struct state* s, struct state* sp)"                        +"\n"+
		            "{"                                                                    +"\n"+
		            "  int* cursor;"                                                       +"\n"+
		            "  s->ptr = 0;"                                                        +"\n"+
		            "  sp->next->ptr = s->ptr;"                                            +"\n"+
		            "  cursor = *sp->next->ptr;"                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            ,
		            },
	/////////////////  7   ///////////////////	
		            {
		            "struct state"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "  struct state* next;"                                                +"\n"+
		            "  int num;"                                                           +"\n"+
		            "  int** ptr;"                                                         +"\n"+
		            "  struct nest nested;"                                                +"\n"+
		            "};"                                                                   +"\n"+
		            ""                                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "void f7(struct state** s)"                                        +"\n"+
		            "{"                                                                    +"\n"+
		            " *s = malloc(sizeof(struct state));"                                  +"\n"+
		            " (*s)->next = 0;"                                                     +"\n"+
		            " (*s)->ptr = 0;"                                                      +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            ,
		            },
				/////////////////  8   ///////////////////	
	            {
	            "#include<stdio.h>"                                                    +"\n"+
	            "#include<stdlib.h>"                                                   +"\n"+
	            "#include<string.h>"                                                   +"\n"+
	            ""                                                                     +"\n"+
	            "void f8(char *p)"                                                   +"\n"+
	            "{"                                                                    +"\n"+
	            "   char zbase;"                                                       +"\n"+
	            "   zbase =*(strrchr (\"hello world\", 'o') + 1);"                       +"\n"+
	            ""                                                                     +"\n"+
	            ""                                                                     +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "NPD_EXP"
	            ,
	            },
/////////////////  9   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            "#include<string.h> "                                                  +"\n"+
		            "struct Student"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "   int age;"                                                          +"\n"+
		            "   char *name;"                                                       +"\n"+
		            "}; "                                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "int f9(int argc, char *argv[])"                                     +"\n"+
		            "{"                                                                    +"\n"+
		            "  struct Student *n;"                                                 +"\n"+
		            "  int i; "                                                            +"\n"+
		            "  n->name=(char*)calloc(10,sizeof(char));"                            +"\n"+
		            "   n->name[0]='a'+0; "                                                +"\n"+
		            "  system(\"PAUSE\");	"                                                  +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            ,
		            },
/////////////////  10   ///////////////////	
	            {
	            "#include <stdio.h>"                                                   +"\n"+
	            "#include <stdlib.h>"                                                  +"\n"+
	            "#include<string.h> "                                                  +"\n"+
	            "struct Student"                                                       +"\n"+
	            "{"                                                                    +"\n"+
	            "   int age;"                                                          +"\n"+
	            "   char *name;"                                                       +"\n"+
	            "}; "                                                                  +"\n"+
	            ""                                                                     +"\n"+
	            "int f10(int argc, char *argv[])"                                     +"\n"+
	            "{"                                                                    +"\n"+
	            "  struct Student *n;"                                                 +"\n"+
	            "  int i; "                                                            +"\n"+
	            "  n->name=(char*)calloc(10,sizeof(char));"                            +"\n"+
	            "  for(i=0;i<10;i++) "                                                +"\n"+
	            "    n->name[i] = 'a'+i; "                                                +"\n"+

	            "  system(\"PAUSE\");	"                                                  +"\n"+
	            "  return 0;"                                                          +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "NPD_EXP"
	            ,
	            },

/////////////////  11   ///////////////////	
	            {
	            "#include <stdio.h>"                                                   +"\n"+
	     		"#include <stdlib.h>"                                                  +"\n"+
	     		"typedef struct { int r, i; } complex;"                                +"\n"+
	            "void f11(int flag)"                                                  +"\n"+
	            "{"                                                                    +"\n"+
	            "    complex *from,*buffer;"                                           +"\n"+
	            "    from = (complex *) calloc(20, sizeof(complex));"                +"\n"+
	    //        "    from = buffer;"                                                   +"\n"+
	            "    if(flag)"                                                         +"\n"+
	            "       for (s = 0; s < 20; s++)"                                      +"\n"+
	            "       {"                                                             +"\n"+
	            "   		from[s].r = s;    "                                             +"\n"+
	            "    		from[s].i = s+1;"                                               +"\n"+
	            "	    }"                                                           +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "NPD_EXP"
	            ,
	            },

/////////////////  12   ///////////////////	
	            {
	            "void f12(int *p)"                                                 +"\n"+
	            "{"                                                                    +"\n"+
	            "	int a = 0;"                                                          +"\n"+
	            "	if (p) {"                                                            +"\n"+
	            "		a = 1;"                                                             +"\n"+
	            "	}"                                                                   +"\n"+
	            "	*(p+1) = 1;//DEFECT, NPD_EXP,p+1"                                    +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "NPD_EXP"
	            ,
	            },
/////////////////  13   ///////////////////	
	            {
	            ""                                                                     +"\n"+
	            "int * f13_1() "                                                     +"\n"+
	            "{"                                                                    +"\n"+
	            "	int * p = (void *)0;"                                                     +"\n"+
	            "	return p;"                                                     +"\n"+
	            "}"                                                                    +"\n"+
	            "void f13_2(int *p)"                                                 +"\n"+
	            "{"                                                                    +"\n"+
	            "	int a = 0;"                                                          +"\n"+
	            "	a = *f13_1();//DEFECT, NPD_EXP,func1_1"                            +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "NPD_EXP"
	            ,
	            },
		 });
	 }
}
