package fault;


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
public class NPD_Check extends ModelTestBase {
	public NPD_Check(String source,String compiletype, String result)
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


	/////////////////  1   ///////////////////	
		            {
		            "void deref(int *p){"                                                  +"\n"+
		            "	*p = *p + 10;"                                                       +"\n"+
		            "}"                                                                    +"\n"+
		            "void rnpd_2(int *t){"                                                 +"\n"+
		            "	deref(t); // NPD_Check"                                              +"\n"+
		            "	if (!t) return;"                                                     +"\n"+
		            "	*t ++;"                                                              +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_Check"
		            ,
		            },

	/////////////////  2   ///////////////////	
		            {
		            "int* p;"                                                              +"\n"+
		            "void f(int a)"                                                        +"\n"+
		            "{"                                                                    +"\n"+
		            "	if(!p)"                                                              +"\n"+
		            "		a++;"                                                               +"\n"+
		            "	*p = a+5;"                                                           +"\n"+
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
