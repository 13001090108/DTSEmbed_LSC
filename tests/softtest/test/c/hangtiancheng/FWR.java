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
public class FWR extends ModelTestBase {
	public FWR(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/rule/FWR-0.1.xml";
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
				//不是误报，但航天城使用很普遍
		            {
		            "typedef unsigned char uchar8; "                                       +"\n"+
		            ""                                                                     +"\n"+
		            "uchar8 f_FWR_1(){"                                                    +"\n"+
		            "     return 0;"                                                       +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },				 
	/////////////////  1   ///////////////////
		        //不是误报，但航天城使用很普遍
		            {
		            "typedef unsigned char uchar8; "                                       +"\n"+
		            ""                                                                     +"\n"+
		            "#define true 1"                                                       +"\n"+
		            "#define false 0"                                                      +"\n"+
		            ""                                                                     +"\n"+
		            "uchar8 f_FWR_1(){"                                                    +"\n"+
		            "     return false;"                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },				 
	/////////////////  2   ///////////////////	
		            {
		            "typedef unsigned char uchar8; /* unsigned 8-bit field */"             +"\n"+
		            ""                                                                     +"\n"+
		            "uchar8 f_FWR_1(){"                                                    +"\n"+
		            "     int num=0;"                                                      +"\n"+
		            "     return num;"                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "FWR"
		            ,
		            },				 
				 
		

		 });
	 }
}
