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
public class SUMU extends ModelTestBase{
	public SUMU(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/SUMU-0.1.xml";
		//fsmPath="softtest/rules/gcc/fault/BO_PRE-0.1.xml";
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
		            "#include <math.h>"                                                    +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "main ()"                                                              +"\n"+
		            "{"                                                                    +"\n"+
		            "	int n = -2;"                                                         +"\n"+
		            "	unsigned int u = 2;"                                                 +"\n"+
		            "	n = n/u;"                                                            +"\n"+
		            "	printf(\"the n is %d\",n);"                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "SUMU"
		            ,
		            },				 
					 				 				 
				 
		 });
	 }
}

