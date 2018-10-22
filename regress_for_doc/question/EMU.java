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
public class EMU extends ModelTestBase{
	public EMU(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/EMU-0.1.xml";
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
		            "typedef enum Q1{Q1Send, Q1Recv} Q1;"                                  +"\n"+
		            "	typedef enum Q2{Q2None, Q2Send, Q2Recv} Q2;"                         +"\n"+
		            "	// Inconsistency between switch variable and case labels"            +"\n"+
		            "	void foo1(Q1 q){"                                                    +"\n"+
		            "	  switch (q){"                                                       +"\n"+
		            "	    case Q2Send: f(); break;"                                        +"\n"+
		            "	    case Q2Recv: g(); break;"                                        +"\n"+
		            "	  }"                                                                 +"\n"+
		            "	}"                                                                   +"\n"+
		            "	//Inconsistency between case labels"                                 +"\n"+
		            "	void foo2(Q1 q){"                                                    +"\n"+
		            "	  switch (q){"                                                       +"\n"+
		            "	    case Q1Send: f(); break;"                                        +"\n"+
		            "	    case Q2Recv: g(); break;"                                        +"\n"+
		            "	  }"                                                                 +"\n"+
		            "	}"                                                                   
		            ,
		            "gcc"
		            ,
		            "EMU"
		            ,
		            },
	 
				 
				 
		 });
	 }
}
