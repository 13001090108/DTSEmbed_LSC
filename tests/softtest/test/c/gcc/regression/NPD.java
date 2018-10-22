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
public class NPD extends ModelTestBase {
	public NPD(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/NPD-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("fault");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
		
		//加载库函数摘要
		LIB_SUMMARYS_PATH="gcc_lib/npd_summary.xml";
		libManager.loadSingleLibFile(LIB_SUMMARYS_PATH);
		libManager.loadSingleLibFile("gcc_lib/lib_summary.xml");
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
		            "#include <stdlib.h>"                                                  +"\n"+
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void ghx_npd_2_f2(int flag,char* to)"                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	char* from;"                                                         +"\n"+
		            "    char* buffer =(char*) calloc(1, 10);"                             +"\n"+
		            "	if(buffer){"                                                         +"\n"+
		            "	}"                                                                   +"\n"+
		            "    if (flag== 0) {"                                                  +"\n"+
		            "		from = to;"                                                         +"\n"+
		            "    }"                                                                +"\n"+
		            "    else {"                                                           +"\n"+
		            "        from = buffer;"                                               +"\n"+
		            "    }"                                                                +"\n"+
		            "    memcpy(from, to, 10);"                                            +"\n"+
		            "	*from;//DEFECT"                                                      +"\n"+
		            "	*buffer;//DEFECT"                                                    +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },
	/////////////////  1   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "int ghx_npd_10_f10 ()"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "  int i;"                                                             +"\n"+
		            "  char * buffer;"                                                     +"\n"+
		            "  scanf (\"%d\", &i);"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "  buffer = (char*) malloc (i+1);"                                     +"\n"+
		            ""                                                                     +"\n"+
		            "  buffer[i]='\\0';//DEFECT"                                            +"\n"+
		            "  printf (\"%s\\n\",buffer);"                                            +"\n"+
		            "  free (buffer);"                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },
	/////////////////  2   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void func()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	int i = 1;"                                                          +"\n"+
		            "	char *ptr;"                                                          +"\n"+
		            ""                                                                     +"\n"+
		            "	ptr = (char*)malloc(i+1);"                                           +"\n"+
		            "	ptr[i]='\\0';//DEFECT"                                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },

	/////////////////  3   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void func()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	char str[] = \"string\";"                                              +"\n"+
		            "	char *ptr;"                                                          +"\n"+
		            "	char tmp;"                                                           +"\n"+
		            ""                                                                     +"\n"+
		            "	ptr = (char*)memchr(str,'p',strlen(str));"                           +"\n"+
		            "	tmp = *ptr; //DEFECT"                                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },

	/////////////////  4   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "void fun(){"                                                          +"\n"+
		            "	int i;"                                                              +"\n"+
		            "	for(i=1;i<10;i++){"                                                  +"\n"+
		            "		char* ch=(char*)malloc(1);"                                         +"\n"+
		            "		*ch='1';     //DEFECT"                                              +"\n"+
		            "	}"                                                                   +"\n"+
		            "	for(i=1;i<10;i++){"                                                  +"\n"+
		            "		char* ch=(char*)malloc(1);"                                         +"\n"+
		            "		*ch='1';     //DEFECT"                                              +"\n"+
		            "	}"                                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },


	/////////////////  5   ///////////////////	
		            {
		            "#include<stdlib.h>"                                                   +"\n"+
		            "#include<stdio.h>"                                                    +"\n"+
		            "#define NELEMS(arr) (sizeof(arr) / sizeof(arr[0]))"                   +"\n"+
		            "int numarray[] = {123, 145, 512, 627, 800, 933};"                     +"\n"+
		            "int numeric (const int *p1, const int *p2){"                          +"\n"+
		            "	return(*p1 - *p2);"                                                  +"\n"+
		            "}"                                                                    +"\n"+
		            "int jhb_npd_13_f1(int key){"                                          +"\n"+
		            "int *itemptr;"                                                        +"\n"+
		            "itemptr = (int *)bsearch (&key, numarray, NELEMS(numarray),"          +"\n"+
		            "						  sizeof(int), (int(*)(const void *,const void *))numeric);"    +"\n"+
		            "return (*itemptr) ;     //DEFECT"                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },



	/////////////////  6   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "#define get_new(type, num)  (type *)malloc(sizeof(type)*num)"         +"\n"+
		            ""                                                                     +"\n"+
		            "int zk_npd_34_f1()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	int *ptr;"                                                           +"\n"+
		            ""                                                                     +"\n"+
		            "	ptr = get_new(int, 1);"                                              +"\n"+
		            ""                                                                     +"\n"+
		            "	return *ptr; //DEFECT"                                               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },

	/////////////////  7   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "int* func1(int *var1, char *var2)"                                    +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (var1 == NULL || var2 == NULL) {"                                 +"\n"+
		            "		*var1 = 0; //DEFECT"                                                +"\n"+
		            "		return NULL;"                                                       +"\n"+
		            "	}"                                                                   +"\n"+
		            "	return var1;"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },
		        	/////////////////  8   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "char* func2(int);"                                                    +"\n"+
		            "char* func3();"                                                       +"\n"+
		            ""                                                                     +"\n"+
		            "void func1(int flag)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *ptr;"                                                          +"\n"+
		            ""                                                                     +"\n"+
		            "	if (flag > 0) {"                                                     +"\n"+
		            "		ptr = func2(flag);"                                                 +"\n"+
		            "	} else {"                                                            +"\n"+
		            "		ptr = func3();"                                                     +"\n"+
		            "	}"                                                                   +"\n"+
		            "	*ptr = 3; //DEFECT"                                                  +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "char* func2(int flag)"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (flag < 0) {"                                                     +"\n"+
		            "		return NULL;"                                                       +"\n"+
		            "	} else {"                                                            +"\n"+
		            "		func3();"                                                           +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "char* func3()"                                                        +"\n"+
		            "{"                                                                    +"\n"+
		            "	return NULL;"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },
		        	///////////////// 9   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "int g_val = 3;"                                                       +"\n"+
		            "int *g_ptr = &g_val;"                                                 +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int);"                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "int func1()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	*g_ptr = 2; //FP"                                                    +"\n"+
		            "	func2(1);"                                                           +"\n"+
		            "	return *g_ptr; //DEFECT"                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int flag)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (flag > 0) {"                                                     +"\n"+
		            "		g_ptr = NULL;"                                                      +"\n"+
		            "	} else {"                                                            +"\n"+
		            "		return;"                                                            +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },
	/////////////////  10   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "int g_val = 3;"                                                       +"\n"+
		            "int *g_ptr = &g_val;"                                                 +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int);"                                                     +"\n"+
		            "void func3();"                                                        +"\n"+
		            "void func4();"                                                        +"\n"+
		            ""                                                                     +"\n"+
		            "int func1()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	*g_ptr = 2; //FP"                                                    +"\n"+
		            "	func2(1);"                                                           +"\n"+
		            "	return *g_ptr; //DEFECT"                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int flag)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (flag > 0) {"                                                     +"\n"+
		            "		g_ptr = NULL;"                                                      +"\n"+
		            "	} else {"                                                            +"\n"+
		            "		return;"                                                            +"\n"+
		            "	}"                                                                   +"\n"+
		            "	func3();"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func3()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	g_ptr = &g_val;"                                                     +"\n"+
		            "	func4();"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func4()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	//g_ptr = 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  11   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "long g_val = 3;"                                                      +"\n"+
		            "long *g_ptr = &g_val;"                                                +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int);"                                                     +"\n"+
		            "void func3();"                                                        +"\n"+
		            "void func4();"                                                        +"\n"+
		            ""                                                                     +"\n"+
		            "int func1()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	*g_ptr = 2; //FP"                                                    +"\n"+
		            "	func2(1);"                                                           +"\n"+
		            "	return *g_ptr; //DEFECT"                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int flag)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (flag > 0) {"                                                     +"\n"+
		            "		g_ptr = NULL;"                                                      +"\n"+
		            "	} else {"                                                            +"\n"+
		            "		return;"                                                            +"\n"+
		            "	}"                                                                   +"\n"+
		            "	func3();"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func3()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	g_ptr = &g_val;"                                                     +"\n"+
		            "	func4();"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func4()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	g_ptr = 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },
	/////////////////  12   ///////////////////	
		            {
		            "void f(char* p){"                                                     +"\n"+
		            "    if(!p){  "                                                        +"\n"+
		            "      return;"                                                        +"\n"+
		            "    }"                                                                +"\n"+
		            "    *p='a'; "                                                         +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  13   ///////////////////	
		            {
		            "void f(char* p){"                                                     +"\n"+
		            "    if(p==0){  "                                                      +"\n"+
		            "       exit(0);"                                                      +"\n"+
		            "    }"                                                                +"\n"+
		            "    *p='a'; "                                                         +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  14   ///////////////////	
		            {
		            "void f(){"                                                            +"\n"+
		            "    char* p;"                                                         +"\n"+
		            "    while(p){"                                                        +"\n"+
		            "       *p;"                                                           +"\n"+
		            "       p=(char*)malloc(11);"                                          +"\n"+
		            "    }"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  15   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                            +"\n"+
		            "void f(){"                                                            +"\n"+
		            "    char* p;"                                                         +"\n"+
		            "    if((p=malloc(11))!=0){"                                             +"\n"+
		            "        *p;"                                                          +"\n"+
		            "    }"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	///////////////// 16   zys 2011.9.23 由于DTS采用的循环机制还是循环计算的区间不准确；另外，指针区间中的UNKNOWN类型与Domain中的unknown标识有点冲突，需要进行统一///////////////////	
		            {
		            "void f(){"                                                            +"\n"+
		            "    char* p=0;"                                                       +"\n"+
		            "    int i;"                                                           +"\n"+
		            "    for(i=1;i<10;i++){"                                               +"\n"+
		            "       p=&i;"                                                         +"\n"+
		            "    } "                                                               +"\n"+
		            "    i=*p;"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  17  ///////////////////	
		            {
		            "void f(int j){"                                                       +"\n"+
		            "    char* p=0;"                                                       +"\n"+
		            "    int i;"                                                           +"\n"+
		            "    for(i=1;i<j;i++){"                                                +"\n"+
		            "       p=&i;"                                                         +"\n"+
		            "    } "                                                               +"\n"+
		            "    i=*p;"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },
		        	/////////////////  18   ///////////////////	
		            {
		            "void f(){"                                                            +"\n"+
		            "    char* p;"                                                         +"\n"+
		            "    if(p=malloc(11) && p!=0){"                                             +"\n"+
		            "        *p;"                                                          +"\n"+
		            "    }"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },


		 });
	 }
}
