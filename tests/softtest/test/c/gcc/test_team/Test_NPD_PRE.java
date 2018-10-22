package softtest.test.c.gcc.test_team;

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
public class Test_NPD_PRE extends ModelTestBase {
	public Test_NPD_PRE(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/NPD_PRE-0.1.xml";
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
		            "void f1(int *x)"                                                      +"\n"+
		            "{"                                                                    +"\n"+
		            "     *x = 5;"                                                         +"\n"+
		            "}"                                                                    +"\n"+
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "     int *p = NULL;"                                                  +"\n"+
		            "     f1(p);//DEFECT"                                                  +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
	/////////////////  1   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "void f1(int *p)"                                                      +"\n"+
		            "{"                                                                    +"\n"+
		            "     *p++;"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            "void f(int i, int j)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "     int *x = NULL;"                                                  +"\n"+
		            "     if(i)"                                                           +"\n"+
		            "         x = &j;"                                                     +"\n"+
		            "     f1(x);//DEFECT"                                                  +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
	/////////////////  2   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "void f2(int *x)"                                                      +"\n"+
		            "{"                                                                    +"\n"+
		            "     *x = 5;  "                                                       +"\n"+
		            "}"                                                                    +"\n"+
		            "void f1(int *x)"                                                      +"\n"+
		            "{"                                                                    +"\n"+
		            "     f2(x);"                                                          +"\n"+
		            "}"                                                                    +"\n"+
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "     int *p = NULL;"                                                  +"\n"+
		            "     f1(p);//DEFECT "                                                 +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
	/////////////////  3   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "void f1(int *x)"                                                      +"\n"+
		            "{"                                                                    +"\n"+
		            "     *x = 11;     "                                                   +"\n"+
		            "}"                                                                    +"\n"+
		            "main()"                                                               +"\n"+
		            "{"                                                                    +"\n"+
		            "     int *p = (int*)malloc(5*sizeof(int));"                           +"\n"+
		            "     f1(&p[3]);//DEFECT"                                              +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	///////////////// 4   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "#include <string.h>"                                                  +"\n"+
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "     char* s = NULL;"                                                 +"\n"+
		            "     s = (char*) malloc (10*sizeof(char));"                           +"\n"+
		            "     strcpy(s, \"abc\");//DEFECT"                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  5   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "int* p;"                                                              +"\n"+
		            "void f1()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "    p = NULL;"                                                        +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "     *p = 5;//DEFECT"                                                 +"\n"+
		            "}"                                                                    +"\n"+
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "     f1();"                                                           +"\n"+
		            "     f2();"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		 });
	 }
}
