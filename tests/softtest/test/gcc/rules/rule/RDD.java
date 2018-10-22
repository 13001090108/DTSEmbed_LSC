package softtest.test.gcc.rules.rule;

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
public class RDD extends ModelTestBase{
	public RDD(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/rule/RDD-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("rule");
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
		            "void static_p(unsigned int p_1, unsigned int p_2, unsigned int p_3,"  +"\n"+
		            "unsigned int p_4,   unsigned int p_5,   unsigned int p_6,"            +"\n"+
		            "unsigned int p_7,   unsigned int p_8,   unsigned int p_9,"            +"\n"+
		            "unsigned int p_10,  unsigned int p_11,  unsigned int p_12,"           +"\n"+
		            "unsigned int p_13,  unsigned int p_14,  unsigned int p_15,"           +"\n"+
		            "unsigned int p_16,  unsigned int p_17,  unsigned int p_18,"           +"\n"+
		            "unsigned int p_19,  unsigned int p_20,  unsigned int p_21)"           +"\n"+
		            "{"                                                                    +"\n"+
		            "    printf(\"RDD\");"                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "RDD"
		            ,
		            },				 
				 
				 
				 
		 });
	 }
}
