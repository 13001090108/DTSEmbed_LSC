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
public class BBU extends ModelTestBase{
	public BBU(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/BBU-0.1.xml";
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
		            "#define true 1"                                                       +"\n"+
		            "#define false 0"                                                      +"\n"+
		            ""                                                                     +"\n"+
		            "void f_BBU(_Bool flags)"                                              +"\n"+
		            "{"                                                                    +"\n"+
		            "    if(flags & 4 == 0){// BBU,defect"                                 +"\n"+
		            "        flags = true;"                                                +"\n"+
		            "    }"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BBU"
		            ,
		            },

				 
		 });
	 }
}

