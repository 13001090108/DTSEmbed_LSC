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
public class Test_UFM extends ModelTestBase {
	public Test_UFM(String source,String compiletype, String result)
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
////////////////	/  0   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "int* p;"                                                              +"\n"+
		            "void f(){"                                                            +"\n"+
		            "	 free(p);"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            "void f1(){"                                                           +"\n"+
		            "     f();"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2(){"                                                           +"\n"+
		            "   p=(int*)malloc(1);"                                                +"\n"+
		            "   f1(); "                                                            +"\n"+
		            "   *p=1; //defect"                                                    +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM"
		            ,
		            },
	/////////////////  1   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "void f1(int i)"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "     int *p = (int*)malloc(1);"                                       +"\n"+
		            "     if(i)"                                                           +"\n"+
		            "         free(p);"                                                    +"\n"+
		            "     *p = 3;//DEFECT"                                                 +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM"
		            ,
		            },
	/////////////////  2   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "int *p;"                                                              +"\n"+
		            "void f(int x, int y)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "     p = (int*)malloc(1);"                                            +"\n"+
		            "     if(x > y)"                                                       +"\n"+
		            "         x++;"                                                        +"\n"+
		            "         else if(x < (y-4))"                                          +"\n"+
		            "             free(p);"                                                +"\n"+
		            "     *p = y; //DEFECT    "                                            +"\n"+
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
