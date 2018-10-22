package softtest.test.gcc.rules.fault;

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
	/////////////////  o  ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "char* ghx_npd_1_f1(int b)"                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	char * p = NULL;"                                                       +"\n"+
		            "	return p;"                                           +"\n"+
		            "}"                                                                    +"\n"+
		            "void ghx_npd_1_f2(char* p)"                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "	char a=*p;"                                                          +"\n"+
		            "}"                                                                    +"\n"+
		            "void ghx_npd_1_f3(int a)"                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "	ghx_npd_1_f2(ghx_npd_1_f1(a));  //defect"                            +"\n"+
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
