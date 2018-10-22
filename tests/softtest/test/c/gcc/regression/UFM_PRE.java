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
public class UFM_PRE extends ModelTestBase {
	public UFM_PRE(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/UFM_PRE-0.1.xml";
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
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int*);"                                                    +"\n"+
		            "int func3(int*);"                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "void func1()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	int *ptr;"                                                           +"\n"+
		            ""                                                                     +"\n"+
		            "	ptr = (int*)malloc(sizeof(int));"                                    +"\n"+
		            "	func2(ptr);"                                                         +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int *ptr)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "		free(ptr);"                                                         +"\n"+
		            "	func3(ptr); //DEFECT"                                                +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int func3(int *ptr)"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	return *ptr;"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM_PRE"
		            ,
		            },
	/////////////////  1   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int, int*);"                                               +"\n"+
		            "int func3(int*);"                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "void func1(int flag)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	int *ptr;"                                                           +"\n"+
		            ""                                                                     +"\n"+
		            "	ptr = (int*)malloc(sizeof(int));"                                    +"\n"+
		            "	if (flag > 0) {"                                                     +"\n"+
		            "		free(ptr);"                                                         +"\n"+
		            "	}"                                                                   +"\n"+
		            "	func2(ptr,0); //DEFECT"                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int *ptr,int n)"                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	func3(ptr);"                                                         +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int func3(int *ptr)"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	return *ptr;"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM_PRE"
		            ,
		            },
	/////////////////  2   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "#define SIZE 5"                                                       +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int, int*);"                                               +"\n"+
		            "int func3(int*);"                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "void func1(int flag)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	int *ptr;"                                                           +"\n"+
		            ""                                                                     +"\n"+
		            "	ptr = (int*)malloc(SIZE*sizeof(int));"                               +"\n"+
		            "	if (flag > 0) {"                                                     +"\n"+
		            "		free(ptr);"                                                         +"\n"+
		            "	}"                                                                   +"\n"+
		            "	func2(0, ptr); //DEFECT"                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int n, int *ptr)"                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	func3(ptr);"                                                         +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int func3(int *ptr)"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	return ptr[SIZE-1];"                                                 +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM_PRE"
		            ,
		            },
	/////////////////  3   ///////////////////	
		          //hcj函数摘要问题，待改进
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "int *g_ptr = NULL;"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int);"                                                     +"\n"+
		            "void func3();"                                                        +"\n"+
		            ""                                                                     +"\n"+
		            "void func1(int flag)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	g_ptr = (int*)malloc(sizeof(int));"                                  +"\n"+
		            "	func2(flag);"                                                        +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int flag)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (flag > 0) {"                                                     +"\n"+
		            "		free(g_ptr);"                                                       +"\n"+
		            "		func3(); //DEFECT"                                                  +"\n"+
		            "	} else {"                                                            +"\n"+
		            "		func3(); //FP"                                                      +"\n"+
		            "		return;"                                                            +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func3()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	(*g_ptr)++;"                                                         +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM_PRE"
		            ,
		            },
	/////////////////  4   ///////////////////	
		          //hcj函数摘要问题，待改进
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "#define SIZE 5"                                                       +"\n"+
		            ""                                                                     +"\n"+
		            "int *g_ptr = NULL;"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int);"                                                     +"\n"+
		            "void func3();"                                                        +"\n"+
		            ""                                                                     +"\n"+
		            "void func1(int flag)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	g_ptr = (int*)malloc(SIZE*sizeof(int));"                             +"\n"+
		            "	func2(flag);"                                                        +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int flag)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (flag > 0) {"                                                     +"\n"+
		            "		free(g_ptr);"                                                       +"\n"+
		            "		func3(); //DEFECT"                                                  +"\n"+
		            "	} else {"                                                            +"\n"+
		            "		func3(); //FP"                                                      +"\n"+
		            "		return;"                                                            +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func3()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	g_ptr[SIZE-1]++;"                                                    +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM_PRE"
		            ,
		            },
	/////////////////  5   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            "typedef struct{"                                                      +"\n"+
		            "   char* p;"                                                          +"\n"+
		            "}S;"                                                                  +"\n"+
		            "S s;"                                                                 +"\n"+
		            "char* p;"                                                             +"\n"+
		            "void  f(){"                                                           +"\n"+
		            "   *(s.p)='a';"                                                       +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f1(){"                                                           +"\n"+
		            "   f();"                                                              +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2(){"                                                           +"\n"+
		            "   free(s.p);"                                                        +"\n"+
		            "}"                                                                    +"\n"+
		            "void f3(){"                                                           +"\n"+
		            "   s.p=malloc(11);"                                                   +"\n"+
		            "   f2();"                                                             +"\n"+
		            "   f1();"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM_PRE"
		            ,
		            },
	/////////////////  6  ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <malloc.h>"                                                  +"\n"+
		            "typedef struct{"                                                      +"\n"+
		            "   char* p;"                                                          +"\n"+
		            "}S;"                                                                  +"\n"+
		            "S s;"                                                                 +"\n"+
		            "char* p;"                                                             +"\n"+
		            "void  f(){"                                                           +"\n"+
		            "   *p='a';"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f1(){"                                                           +"\n"+
		            "   f();"                                                              +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2(){"                                                           +"\n"+
		            "   free(p);"                                                          +"\n"+
		            "}"                                                                    +"\n"+
		            "void f3(){"                                                           +"\n"+
		            "   p=malloc(11);"                                                     +"\n"+
		            "   f2();"                                                             +"\n"+
		            "   f1();"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM_PRE"
		            ,
		            },
	/////////////////  7   ///////////////////	
		            {
		            "  #include <stdlib.h>"                                                +"\n"+
		            "  struct s{"                                                          +"\n"+
		            "      int *j;"                                                        +"\n"+
		            "  };"                                                                 +"\n"+
		            "  struct e{"                                                          +"\n"+
		            "      struct s * x;  "                                                +"\n"+
		            "  }g;"                                                                +"\n"+
		            "  "                                                                   +"\n"+
		            "  void func() {"                                                      +"\n"+
		            "      *g.x =1;"                                                       +"\n"+
		            "  "                                                                   +"\n"+
		            "  }"                                                                  +"\n"+
		            "  "                                                                   +"\n"+
		            "  int *foo(int t) {"                                                  +"\n"+
		            "      "                                                               +"\n"+
		            "      (g.x)->j = (int *)malloc(1);"                                   +"\n"+
		            "      if (!t) {"                                                      +"\n"+
		            "          free(g.x);"                                                 +"\n"+
		            "      }"                                                              +"\n"+
		            "      func();"                                                        +"\n"+
		            "      return 0;"                                                      +"\n"+
		            " }"                                                                   
		            ,
		            "gcc"
		            ,
		            "UFM_PRE"
		            ,
		            },
	/////////////////  0   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "char *p[10];"                                                         +"\n"+
		            "void foo_6_5() {"                                                     +"\n"+
		            "	*p[0] = 'a';"                                                        +"\n"+
		            "}"                                                                    +"\n"+
		            "int bar_6_5() {"                                                      +"\n"+
		            "	p[0] = (char *)malloc(sizeof(char));"                                +"\n"+
		            "	free(p[0]);"                                                         +"\n"+
		            "	foo_6_5();"                                                          +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM_PRE"
		            ,
		            },
		 });
	 }
}
