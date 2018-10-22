package question;

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
public class CCW extends ModelTestBase{
	public CCW(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/CCW-0.1.xml";
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
	/////////////////  1   ///////////////////	
		            {
		            "void foo() {"                                                         +"\n"+
		            "  int x = 3;"                                                         +"\n"+
		            "  while (x = 3)   // defect - the condition is constant"              +"\n"+
		            "  {"                                                                  +"\n"+
		            "      	x++;"                                                          +"\n"+
		            "  } "                                                                 +"\n"+
		            "// Ok - typical usage of 'do' construct when a user wants to //organize a infinite loop     "+"\n"+
		            "  while (true)    "                                                   +"\n"+
		            "  {"                                                                  +"\n"+
		            "      	/* ... */"                                                     +"\n"+
		            "  }"                                                                  +"\n"+
		            " }"                                                                   
		            ,
		            "gcc"
		            ,
		            "CCW"
		            ,
		            },

		 });
	 }
}


