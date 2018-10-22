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
public class Test_UFM_PRE extends ModelTestBase{
	public Test_UFM_PRE(String source,String compiletype, String result)
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
////////////////	/  0   ///////////////////	
		            {
		            "#include <stdlib.h>"                                             +"\n"+
		            "void f(int* p){"                                                      +"\n"+
		            "	 *p=1;"                                                              +"\n"+
		            "}"                                                                    +"\n"+
		            "void f1(int* p){"                                                     +"\n"+
		            "     f(p);"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2(){"                                                           +"\n"+
		            "   int *p=(int*)malloc(1);"                                           +"\n"+
		            "   free(p);"                                                          +"\n"+
		            "   f1(p); //defect"                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM_PRE"
		            ,
		            },
////////////////	/1   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                +"\n"+
		            "int* p;"                                                              +"\n"+
		            "void f(){"                                                            +"\n"+
		            "	 *p=1;"                                                              +"\n"+
		            "}"                                                                    +"\n"+
		            "void f1(){"                                                           +"\n"+
		            "     f();"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2(){"                                                           +"\n"+
		            "   p=(int*)malloc(1);"                                                +"\n"+
		            "   free(p);"                                                          +"\n"+
		            "   f1(); //defect"                                                    +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM_PRE"
		            ,
		            },
	/////////////////  2   ///////////////////	
		            //hcj此处用到内存释放特征(有条件的内存释放被认为内存不被释放)
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "void f1(int *p, int a)"                                               +"\n"+
		            "{"                                                                    +"\n"+
		            "     if(a>5)"                                                         +"\n"+
		            "         free(p);"                                                    +"\n"+
		            "     else"                                                            +"\n"+
		            "         a++;     "                                                   +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f(int x)"                                                        +"\n"+
		            "{"                                                                    +"\n"+
		            "     int* p = (int*)malloc(10);"                                      +"\n"+
		            "     f1(p, x);"                                                       +"\n"+
		            "     int *q;"                                                         +"\n"+
		            "     q = p;//DEFECT     "                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  3   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "void f1(int* p)"                                                      +"\n"+
		            "{"                                                                    +"\n"+
		            "     *p = 3;    "                                                     +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f(int x)"                                                        +"\n"+
		            "{"                                                                    +"\n"+
		            "     int* p = (int*)malloc(1);"                                       +"\n"+
		            "     if(x)"                                                           +"\n"+
		            "         free(p);"                                                    +"\n"+
		            "     f1(p);//DEFECT "                                                 +"\n"+
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
