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
public class NUAV extends ModelTestBase{
	public NUAV(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/NUAV-0.1.xml";
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
		            "long foo(long arr[]) {"                                               +"\n"+
		            "	long time1 = 0;"                                                     +"\n"+
		            "	long time2 = 0;"                                                     +"\n"+
		            "	long len = 0;"                                                       +"\n"+
		            "	int i = 0;"                                                          +"\n"+
		            "	for (i = 0; i < sizeof(arr); i += 2) {"                              +"\n"+
		            "		time1 = arr[i];"                                                    +"\n"+
		            "		time1 = arr[i + 1];//NUAV,time1,defect"                             +"\n"+
		            "		if (time1 < time2) {"                                               +"\n"+
		            "			long d = time1 - time2;"                                           +"\n"+
		            "			if (d > len) len = d;"                                             +"\n"+
		            "		}"                                                                  +"\n"+
		            "	}"                                                                   +"\n"+
		            "	return len;"                                                         +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NUAV"
		            ,
		            },
				 
				 
		 });
	 }
}

