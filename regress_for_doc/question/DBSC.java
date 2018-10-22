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
public class DBSC extends ModelTestBase{
	public DBSC(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/DBSC-0.1.xml";
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
	///////////////// 1   ///////////////////	
		            {
		            "void setValue(int a){"                                                +"\n"+
		            "      		int I=0;"                                                     +"\n"+
		            "      		if(a<=0){"                                                    +"\n"+
		            "      			i++;"                                                        +"\n"+
		            "      		}"                                                            +"\n"+
		            "      		else{"                                                        +"\n"+
		            "      			i++;"                                                        +"\n"+
		            "      		}"                                                            +"\n"+
		            "      }"                                                              
		            ,
		            "gcc"
		            ,
		            "DBSC"
		            ,
		            },

	/////////////////  2   ///////////////////	
		            {
		            "void setValue(int a){"                                                +"\n"+
		            "      		int i=0;"                                                     +"\n"+
		            "      		switch(a){"                                                   +"\n"+
		            "      		case 1:"                                                      +"\n"+
		            "      			i++;"                                                        +"\n"+
		            "      			break;"                                                      +"\n"+
		            "      		case 2:"                                                      +"\n"+
		            "      			i++;"                                                        +"\n"+
		            "      			break;"                                                      +"\n"+
		            "      	   default:"                                                   +"\n"+
		            "      			i--;"                                                        +"\n"+
		            "      	}"                                                             +"\n"+
		            "      }"                                                              
		            ,
		            "gcc"
		            ,
		            "DBSC"
		            ,
		            },
				 
				 
				 
				 
		 });
	 }
}

