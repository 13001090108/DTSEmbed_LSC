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
public class FCF extends ModelTestBase{
	public FCF(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/FCF-0.1.xml";
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
		            "main(){"                                                              +"\n"+
		            "	         float value1;"                                              +"\n"+
		            "	         float value2;"                                              +"\n"+
		            "	         if(value1==value2)"                                         +"\n"+
		            "	            printf(\"They are equal\");"                               +"\n"+
		            "	         else"                                                       +"\n"+
		            "	            printf(\"They are not equal\");"                           +"\n"+
		            "     }"                                                               
		            ,
		            "gcc"
		            ,
		            "FCF"
		            ,
		            },

				 
				 
		 });
	 }
}


