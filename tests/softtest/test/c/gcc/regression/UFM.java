package softtest.test.c.gcc.regression;

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
public class UFM extends ModelTestBase {
	public UFM(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/UFM-0.1.xml";
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

	/////////////////  0  ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            "typedef struct{"                                                      +"\n"+
		            "   char* p;"                                                          +"\n"+
		            "}S;"                                                                  +"\n"+
		            "S s;"                                                                 +"\n"+
		            "char* p;"                                                             +"\n"+
		            "void f(){"                                                            +"\n"+
		            "   p=(char*)malloc(11);"                                              +"\n"+
		            "   free(p);"                                                          +"\n"+
		            "   *(p);"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM"
		            ,
		            },

	   ///////////////   1    /////////////////
                {
	                "#include <stdlib.h>"                                                  +"\n"+
                    "void test1(){"                                                        +"\n"+
                    "	int *memleak_error1=NULL;"                                           +"\n"+
                    "	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
                    "	free(memleak_error1);"                                               +"\n"+
                    "	*memleak_error1 = 1;//DEFECT, UFM, memleak_error1"                   +"\n"+
                    "}" 
                    ,
                    "gcc"
                    ,
                    "UFM"
                    ,
                    },
      ///////////////    2    ////////////////
	                {
	                "#include <stdlib.h>"                                                  +"\n"+
	                "int* i;"                                                              +"\n"+
	                "void f(int *i){"                                                      +"\n"+
	                "   free(i);"                                                          +"\n"+
	                "}"                                                                    +"\n"+
	                "void f1(){"                                                           +"\n"+
	                "   i=(int*)malloc(1);"                                                +"\n"+
	                "   f(i);"                                                             +"\n"+
	                "   *i;//DEFECT"                                                       +"\n"+
	                "}"                                                                    
	                ,
	                "gcc"
                    ,
	                "UFM"
	                ,
	                },

	  ///////////////     3    //////////////
                    {
	                "#include <stdlib.h>"                                                  +"\n"+
                    "void test2(){"                                                        +"\n"+
                    "	int *memleak_error1=NULL;"                                           +"\n"+
                    "	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
                    "	free(memleak_error1);"                                               +"\n"+
                    "	return memleak_error1;//DEFECT, UFM, memleak_error1"               +"\n"+
                    "}"                                                                    
                    ,
                    "gcc"
                    ,
                    "UFM"
                    ,
                    },
    /////////////////  4   ///////////////////	
                    {
                    "#include<stdio.h>"                                                    +"\n"+
                    "#include<stdlib.h>"                                                   +"\n"+
                    "int main(){"                                                          +"\n"+
                    "   int *table;"                                                       +"\n"+
                    "   //table = (int *)malloc(sizeof(int));"                               +"\n"+
                    "   free (table);  // Wrong defect"                                    +"\n"+
                    "}"                                                                    
                    ,
                    "gcc"
                    ,
                    "OK"
                    ,
                    },
    /////////////////  5   ///////////////////	
                    {
                    "#include <stdlib.h>"                                                  +"\n"+
                    "int foo_1_2(char *f,int s) {"                                               +"\n"+
                    "	f = (char*)malloc(sizeof(char));"                                    +"\n"+
                    "	free(f);"                                                            +"\n"+
                    "	if (s)"                                                              +"\n"+
                    "		*f = 'a';"                                                          +"\n"+
                    "	return 0;"                                                           +"\n"+
                    "}"                                                                    
                    ,
                    "gcc"
                    ,
                    "UFM"
                    ,
                    },
    /////////////////  6   ///////////////////	
                    {
                    "#include <stdlib.h>"                                                  +"\n"+
                    "char *p;"                                                             +"\n"+
                    "void foo_8_2(char * p) {"                                               +"\n"+
                    "   *p;"                                                                    +"\n"+
                    "}"                                                                    +"\n"+
                    "void bar_8_2() {"                                                     +"\n"+
                    "	p = (char *)malloc(sizeof(char));"                                   +"\n"+
                    "	free(p);"                                                            +"\n"+
                    "	foo_8_2(p);"                                                        +"\n"+
                    "}"                                                                    
                    ,
                    "gcc"
                    ,
                    "UFM"
                    ,
                    },
    /////////////////  7   ///////////////////	
                    {
                    "#include <stdlib.h>"                                                  +"\n"+
                    "void myfree_1_10(char *f) {"                                          +"\n"+
                    "	free(f);"                                                            +"\n"+
                    "}"                                                                    +"\n"+
                    "void bar_1_10(char * f) {"                                            +"\n"+
                    "	myfree_1_10(f);"                                                     +"\n"+
                    "}"                                                                    +"\n"+
                    "int main() {"                                                     +"\n"+
                    "    char *f;"                                                         +"\n"+
                    "	f = (char*)malloc(sizeof(char));"                                    +"\n"+
                    "	bar_1_10(f);"                                                        +"\n"+
                    "	*f = 'a';"                                                           +"\n"+
                    "	return 0;"                                                           +"\n"+
                    "}"                                                                    
                    ,
                    "gcc"
                    ,
                    "UFM"
                    ,
                    },
                	/////////////////  8   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            "typedef struct{"                                                      +"\n"+
		            "   char* p;"                                                          +"\n"+
		            "}S;"                                                                  +"\n"+
		            "S s;"                                                                 +"\n"+
		            ""                                                                     +"\n"+
		            "void f(){"                                                            +"\n"+
		            "   s.p=(char*)malloc(11);"                                            +"\n"+
		            "   free(s.p);"                                                        +"\n"+
		            "   *(s.p);"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM"
		            ,
		            },

	/////////////////  9   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            "typedef struct{"                                                      +"\n"+
		            "   char* p;"                                                          +"\n"+
		            "}S;"                                                                  +"\n"+
		            "S s;"                                                                 +"\n"+
		            "char* f(){"                                                           +"\n"+
		            "   return  (char*)malloc(11);"                                        +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f(){"                                                            +"\n"+
		            "   s.p=f();"                                                          +"\n"+
		            "   free(s.p);"                                                        +"\n"+
		            "   *(s.p);"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM"
		            ,
		            },
		            /////////////////  10   ///////////////////	
                    {
                    "#include <stdlib.h>"                                                  +"\n"+
                    "void myfree_2_9(char *f) {"                                           +"\n"+
                    "	free(f);"                                                            +"\n"+
                    "}"                                                                    +"\n"+
                    "struct A_2_9 {"                                                       +"\n"+
                    "	char *f;"                                                            +"\n"+
                    "};"                                                                   +"\n"+
                    "int foo_2_9() {"                                                      +"\n"+
                    "	struct A_2_9 a;"                                                     +"\n"+
                    "	a.f = (char*)malloc(sizeof(char));"                                  +"\n"+
                    "	myfree_2_9(a.f);"                                                    +"\n"+
                    "	*a.f = 'a';"                                                         +"\n"+
                    "	return 0;"                                                           +"\n"+
                    "}"                                                                    
                    ,
		            "gcc"
		            ,
		            "UFM"
		            ,
                    },
    /////////////////  11   ///////////////////	
                    {
                    "#include <stdlib.h>"                                                  +"\n"+
                    "struct A_8_3 {"                                                       +"\n"+
                    "	char *p;"                                                            +"\n"+
                    "};"                                                                   +"\n"+
                    "struct A_8_3 a;"                                                      +"\n"+
                    "void foo_8_3(char * p) {"                                             +"\n"+
                    "     *p;"                                                             +"\n"+
                    "}"                                                                    +"\n"+
                    "void bar_8_3() {"                                                     +"\n"+
                    "	a.p = (char *)malloc(sizeof(char));"                                 +"\n"+
                    "	free(a.p);"                                                          +"\n"+
                    "	foo_8_3(a.p);"                                                       +"\n"+
                    "}"                                                                    
                    ,
                    "gcc"
                    ,
                    "UFM"
                    ,
                    },
                    /////////////////  12   ///////////////////	
                    {
                    "#include <stdlib.h>"                                                  +"\n"+
                    "void myfree_4_10(char *p) {"                                          +"\n"+
                    "	free(p);"                                                            +"\n"+
                    "}"                                                                    +"\n"+
                    "void foo_4_10(char * p) {"                                            +"\n"+
                    "	myfree_4_10(p);"                                                     +"\n"+
                    "}"                                                                    +"\n"+
                    "int bar_4_10() {"                                                     +"\n"+
                    "    char *f[10];"                                                     +"\n"+
                    "	f[0] = (char*)malloc(sizeof(char));"                                 +"\n"+
                    "	//myfree_4_10(f);"                                                   +"\n"+
                    "	foo_4_10(f[0]);"                                                     +"\n"+
                    "	* f[0] = 1;"                                                         +"\n"+
                    "	return 0;"                                                           +"\n"+
                    "}"                                                                    
                    ,
                    "gcc"
                    ,
                    "UFM"
                    ,
                    },

		 });
	 }
}
