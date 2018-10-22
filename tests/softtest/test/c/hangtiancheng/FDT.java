package softtest.test.c.hangtiancheng;

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
public class FDT extends ModelTestBase{
	public FDT(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/FDT-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("fault");
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
		            "void f_FDT_3(){"                                                      +"\n"+
		            "     unsigned int DRAM ;"                                             +"\n"+
		            "     DRAM = DRAM & 0xFFFF;//FDT,false alarm"                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  1   ///////////////////	
		            {
		            "void f_FDT_4(){"                                                      +"\n"+
		            "     unsigned int DRAM ;"                                             +"\n"+
		            "     int num=-100;"                                                    +"\n"+
		            "     DRAM = num & 0xFFFF;//FDT,defect"                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "FDT"
		            ,
		            },	 
    /////////////////  2   ///////////////////	
		            {
		            "void f_FDT_4(){"                                                      +"\n"+
		            "     unsigned int DRAM ;"                                             +"\n"+
		            "     DRAM = 0xFF;//FDT,false alarm"                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },			 
				 
		 });
	 }
}
		