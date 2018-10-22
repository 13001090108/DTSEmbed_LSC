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
public class IAO extends ModelTestBase{
	public IAO(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/IAO-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("fault");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
			
		//加载库函数摘要
		LIB_SUMMARYS_PATH="gcc_lib/lib_summary.xml";
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
		            "int test1(int a) {"                                                   +"\n"+
		            "	if(a<10 && a>-1){"                                                   +"\n"+
		            "		int result=10/a; // DEFECT, IAO, "                                  +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "IAO"
		            ,
		            },

	/////////////////  2   ///////////////////	
		            {
		            "int test1(int a) {"                                                   +"\n"+
		            "	if(a<10 && a>-1){"                                                   +"\n"+
		            "		int result=10/a; // DEFECT, IAO, "                                  +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "IAO"
		            ,
		            },
		            
	/////////////////  3   ///////////////////	
		            {
		            "int func3()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	int a = 0, b = 10;"                                                  +"\n"+
		            "	b /= a; // DEFECT, IAO, "                                            +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "IAO"
		            ,
		            },
		            
	/////////////////  4   ///////////////////	
		            {
		            ""                                                                     
		            ,
		            "gcc"
		            ,
		            "IAO"
		            ,
		            },

	/////////////////  5   ///////////////////	
		            {
		            "void f1(){"                                                           +"\n"+
		            "	float i = 5.0; "                                                     +"\n"+
		            "	float b=asin(i);"                                                    +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "IAO"
		            ,
		            },
		            
	/////////////////  6   ///////////////////	
		            {
		            "int func1()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	int a = 0;"                                                          +"\n"+
		            "	div(10, a); // DEFECT, IAO_PRE, "                                    +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "IAO"
		            ,
		            },
		            
	/////////////////  7   ///////////////////	
		            {
		            "int func2()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	int a = 0;"                                                          +"\n"+
		            "	ldiv(10, a); // DEFECT, IAO_PRE, "                                   +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "IAO"
		            ,
		            },

	/////////////////  8   ///////////////////	
		            {
		            "int func3()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	double a = -1.0;"                                                    +"\n"+
		            "	double b = log(a); // DEFECT, IAO_PRE, "                             +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "IAO"
		            ,
		            },


		 });
	 }
}
