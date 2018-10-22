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
public class LS extends ModelTestBase{
	public LS(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/LS-0.1.xml";
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
		            "#include <pthread.h>	  "                                              +"\n"+
		            " void foo(pthread_mutex_t *mutex) {"                                  +"\n"+
		            "		 pthread_mutex_lock(mutex);   //defect"                             +"\n"+
		            "		  sleep(30000);"                                                    +"\n"+
		            "		  pthread_mutex_unlock(mutex);"                                     +"\n"+
		            " }"                                                                   
		            ,
		            "gcc"
		            ,
		            "LS"
		            ,
		            },



	 
		 });
	 }
}


