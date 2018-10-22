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
public class AOOP extends ModelTestBase{
	public AOOP(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/rule/AOOP-0.1.xml";
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
		            "void f_AOOP_1() {"                                                    +"\n"+
		            "     int a[5] ={0};"                                                  +"\n"+
		            "     int *p = a;"                                                     +"\n"+
		            "     int w = *(p+10);//AOOP     "                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "AOOP"
		            ,
		            },
	/////////////////  1   ///////////////////	
		            {
		            "void f_AOOP_2(int a[]) {"                                             +"\n"+
		            "     int *p = a;"                                                     +"\n"+
		            "     int n = *(p+100);//AOOP  "                                       +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "AOOP"
		            ,
		            },		            
		            
				 
		 });
	 }
}

