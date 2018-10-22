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
public class BO_PRE extends ModelTestBase{
	public BO_PRE(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/BO_PRE-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("fault");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
		
		//加载库函数摘要
		LIB_SUMMARYS_PATH="gcc_lib/bo_summary.xml";
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
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "char g_array[10];"                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(char*);"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void func1()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *str = \"This is a too long string\";"                            +"\n"+
		            ""                                                                     +"\n"+
		            "	func2(str); //DEFECT"                                                +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(char *ptr)"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "	strcpy(g_array, ptr);"                                               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO_PRE"
		            ,
		            },
	/////////////////  1   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "char g_array[10];"                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int, char*, int);"                                         +"\n"+
		            "void func3(int, char*);"                                              +"\n"+
		            ""                                                                     +"\n"+
		            "void func1(int flag)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *str = \"This is a too long string\";"                            +"\n"+
		            "	int len = strlen(str);"                                              +"\n"+
		            ""                                                                     +"\n"+
		            "	func2(len, str, flag); //DEFECT"                                     +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int len, char *ptr, int flag)"                             +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (flag > 0) {"                                                     +"\n"+
		            "		strcpy(g_array, ptr);"                                              +"\n"+
		            "	} else {"                                                            +"\n"+
		            "		func3(len, ptr);"                                                   +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func3(int len, char *ptr)"                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "	strncpy(g_array, ptr, len);"                                         +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO_PRE"
		            ,
		            },
	/////////////////  2   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "char g_array[10];"                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int, char*, int);"                                         +"\n"+
		            "void func3(int, int, char*);"                                         +"\n"+
		            ""                                                                     +"\n"+
		            "void func1(int flag)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *str = \"This is a too long string\";"                            +"\n"+
		            ""                                                                     +"\n"+
		            "	func2(0, str, flag); //DEFECT"                                       +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int n, char *ptr, int flag)"                               +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (flag > 0) {"                                                     +"\n"+
		            "		return;"                                                            +"\n"+
		            "	} else {"                                                            +"\n"+
		            "		func3(0, 0, ptr);"                                                  +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func3(int n, int m, char *ptr)"                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	strcat(g_array, ptr);"                                               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO_PRE"
		            ,
		            },

	/////////////////  3  ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <string.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "struct S{"                                                            +"\n"+
		            "   char a[12];"                                                       +"\n"+
		            "   char b[34];"                                                       +"\n"+
		            "}s1;"                                                                 +"\n"+
		            "char* p;"                                                             +"\n"+
		            "void f(){"                                                            +"\n"+
		            "   strcpy(s1.a,p);"                                                   +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f1(){"                                                           +"\n"+
		            "     f(); "                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            "void  f2(){"                                                          +"\n"+
		            "     p=(char*)malloc(111);"                                           +"\n"+
		            "     f1(); "                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO_PRE"
		            ,
		            },
	/////////////////  4   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <string.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "struct S{"                                                            +"\n"+
		            "   char a[12];"                                                       +"\n"+
		            "   char b[34];"                                                       +"\n"+
		            "}s1;"                                                                 +"\n"+
		            "char* p;"                                                             +"\n"+
		            "void f(char* q){"                                                     +"\n"+
		            "   strcpy(s1.a,q);"                                                   +"\n"+
		            "}"                                                                    +"\n"+
		            "void f1(int i,char* q){"                                              +"\n"+
		            "     f(q); "                                                          +"\n"+
		            "}"                                                                    +"\n"+
		            "void  f2(){"                                                          +"\n"+
		            "     p=(char*)malloc(111);"                                           +"\n"+
		            "     f1(1,p); "                                                       +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO_PRE"
		            ,
		            },
	/////////////////  5   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <string.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "int* f(){"                                                            +"\n"+
		            "   return (int*)malloc(11);"                                          +"\n"+
		            "}"                                                                    +"\n"+
		            "void f1(int *p){"                                                     +"\n"+
		            "   int a[5];"                                                         +"\n"+
		            "   strcpy(a,p);"                                                      +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2(){"                                                           +"\n"+
		            "   f1(f()); "                                                         +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO_PRE"
		            ,
		            },


		            

		 });
	 }
}
