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
public class Test_NPD_PARAM extends ModelTestBase {
	public Test_NPD_PARAM(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/NPD_PARAM-0.1.xml";
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
		            "void f1(int *p)"                                                      +"\n"+
		            "{"                                                                    +"\n"+
		            "     int i = *p;"                                                     +"\n"+
		            "}"                                                                    +"\n"+
		            "int* f2()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "     return NULL;"                                                    +"\n"+
		            "}"                                                                    +"\n"+
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "     f1(f2());//DEFECT"                                               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PARAM"
		            ,
		            },
	/////////////////  1   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "void f1(int *p)"                                                      +"\n"+
		            "{"                                                                    +"\n"+
		            "     int i = *p;"                                                     +"\n"+
		            "}"                                                                    +"\n"+
		            "int* f2()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "     return (int*) malloc(sizeof(int));"                              +"\n"+
		            "}"                                                                    +"\n"+
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "     f1(f2());//DEFECT"                                               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PARAM"
		            ,
		            },

		 });
	 }
}
