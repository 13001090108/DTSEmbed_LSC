package softtest.test.gcc.rules.question;

import java.util.Arrays;
import java.util.Collection;

import org.junit.BeforeClass;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import softtest.fsm.c.FSMLoader;
import softtest.fsm.c.FSMMachine;
import softtest.fsmanalysis.c.FSMAnalysisVisitor;
import softtest.test.c.rules.ModelTestBase;

@RunWith(Parameterized.class)
public class PARAM extends ModelTestBase{
	public PARAM(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/PARAM-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("question");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
	}
	 @Parameters
	 public static Collection<Object[]> testcaseAndResults()
	 {
		 return Arrays.asList(new Object[][] {
	/////////////////  0   ///////////////////	
		            {
		            "struct ugly {"                                                        +"\n"+
		            "  	int x[20];"                                                        +"\n"+
		            "  	char y[100];"                                                      +"\n"+
		            "  	int z[20];"                                                        +"\n"+
		            "};"                                                                   +"\n"+
		            ""                                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "void foo(struct ugly arg) {}"                                         
		            ,
		            "gcc"
		            ,
		            "PARAM"
		            ,
		            },
	/////////////////  1   ///////////////////	
		            {
		            "void fun(int a, int b, char b)"                                       +"\n"+
		            "{}"                                                                   
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  3   ///////////////////	
		            {
		            "void fun(int a, int b, char b)"                                       +"\n"+
		            "{}"                                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void fun1(int a, int b, int c, int d){}"                              +"\n"+
		            ""                                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "void fun2(int a);"                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
				 
		 });
	 }
}
