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
public class Test_NPD_CHECK extends ModelTestBase {
	public Test_NPD_CHECK(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/NPD_CHECK-0.1.xml";
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
		            "void f(int* p)"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "    int i = 1;"                                                       +"\n"+
		            "    if(p!=0)"                                                         +"\n"+
		            "        i++;"                                                         +"\n"+
		            "    int j = i - *p;//DEFECT     "                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  1   ///////////////////	
		            {
		            "void f(int* p)"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "    int i = 1;"                                                       +"\n"+
		            "    int j = i - *p;//DEFECT    "                                      +"\n"+
		            "    if(p==0)"                                                         +"\n"+
		            "        i--;        "                                                 +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_Check"
		            ,
		            },


		 });
	 }
}
