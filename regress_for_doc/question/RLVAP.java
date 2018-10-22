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
public class RLVAP extends ModelTestBase{
	public RLVAP(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/RLVAP-0.1.xml";
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
		            "#include <stdlib.h>"                                                  +"\n"+
		            " int *func_RET(unsigned n)"                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "      			int aux;"                                                    +"\n"+
		            "      			int *p;"                                                     +"\n"+
		            "      			if (n == 1) {"                                               +"\n"+
		            "          				p = &aux;   //defect"                                   +"\n"+
		            "	      			} else {"                                                   +"\n"+
		            "          				p = (int *)malloc(n * sizeof(int));"                    +"\n"+
		            "	      			}"                                                          +"\n"+
		            "      			return p;"                                                   +"\n"+
		            " 	}"                                                                  
		            ,
		            "gcc"
		            ,
		            "RLVAP"
		            ,
		            },


				 
		 });
	 }
}


