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
public class Test_NPD_POST extends ModelTestBase {
	public Test_NPD_POST(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/NPD_POST-0.1.xml";
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
		            "int *p;"                                                              +"\n"+
		            "void f1()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "     p = 0;     "                                                     +"\n"+
		            "}"                                                                    +"\n"+
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "     f1();"                                                           +"\n"+
		            "     *p = 3;//DEFECT"                                                 +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_POST"
		            ,
		            },
	/////////////////  1   ///////////////////	
		            {
		            "int *p;"                                                              +"\n"+
		            "void f1()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "     p = 0;     "                                                     +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2(int x)"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "     p = &x;     "                                                    +"\n"+
		            "}"                                                                    +"\n"+
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "     int x = 7;"                                                      +"\n"+
		            "     f1();"                                                           +"\n"+
		            "     f2(x);"                                                          +"\n"+
		            "     *p= *p + 5;"                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  2   ///////////////////	
		            {
		            "int* p;"                                                              +"\n"+
		            "void f1()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "     p = 0;"                                                          +"\n"+
		            "     "                                                                +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f2()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "     f1();"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "     f2();"                                                           +"\n"+
		            "     *p++;//DEFECT"                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_POST"
		            ,
		            },
	/////////////////  3   ///////////////////	
		            //f1的后置信息没取到
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "int* p;"                                                              +"\n"+
		            "void f1()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "     if(p == NULL)"                                                   +"\n"+
		            "         p = (int*)malloc(1);"                                        +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "     f1();"                                                           +"\n"+
		            "     *p = 2;//DEFECT"                                                 +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_POST"
		            ,
		            },

	/////////////////  4   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "int* p;"                                                              +"\n"+
		            "int* f2()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "     return NULL;"                                                    +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f1()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "     p = f2();"                                                       +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "     f1();"                                                           +"\n"+
		            "     *p = 1;//DEFECT"                                                 +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_POST"
		            ,
		            },
	/////////////////  5   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "int* p;"                                                              +"\n"+
		            "void f1()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "     *p++;     "                                                      +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f2()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "     p = NULL;"                                                       +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f(int i)"                                                        +"\n"+
		            "{"                                                                    +"\n"+
		            "     *p = 7;"                                                         +"\n"+
		            "     if(i >0)"                                                        +"\n"+
		            "         f1();"                                                       +"\n"+
		            "     else f2();"                                                      +"\n"+
		            "     *p++;//DEFECT    "                                               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_POST"
		            ,
		            },




		 });
	 }
}
