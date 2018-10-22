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
public class GLOB extends ModelTestBase{
	public GLOB(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/GLOB-0.1.xml";
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
		           
		            "	int *buf;"                                                           +"\n"+
		            "	void func_GLOB(unsigned n)"                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	      		int aux;"                                                    +"\n"+
		            "	      		if (n == 1) {"                                               +"\n"+
		            "	          			buf = &aux;   //defect"                                 +"\n"+
		            "	      		} else {"                                                    +"\n"+
		            "	          			buf = (int *)malloc(n * sizeof(int));"                  +"\n"+
		            "	      		}"                                                           +"\n"+
		         
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "GLOB"
		            ,
		            },
	/////////////////  0   ///////////////////	
		            {
		           
		            "	int *buf;"                                                           +"\n"+
		            "	void func_GLOB(unsigned n)"                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	      		int aux;"                                                    +"\n"+
		            "	      		if (n == 1) {"                                               +"\n"+
		            "	          			buf = &aux; "                                           +"\n"+
		            "                        buf = (int *)malloc(n * sizeof(int));"        +"\n"+
		            "	      		} else {"                                                    +"\n"+
		            "	          			buf = (int *)malloc(n * sizeof(int));"                  +"\n"+
		            "	      		}"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },

	/////////////////  2  ///////////////////	
		            {
			                                               
			            "	int *buf;"                                                           +"\n"+
			            "	void func_GLOB(unsigned n)"                                          +"\n"+
			            "{"                                                                    +"\n"+
			            "	      		int aux;"                                                    +"\n"+
			            "	      		if (n == 1) {"                                               +"\n"+
			            "	          			buf = &aux; "                                           +"\n"+
		
			            "	      		} else {"                                                    +"\n"+
			            "	          			buf = (int *)malloc(n * sizeof(int));"                  +"\n"+
			            "	      		}"                                                           +"\n"+
			            "	      		buf =  &aux;"                                                           +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "GLOB"
			            ,
			            },
		/////////////////  0   ///////////////////	
			            {
			           
			            "	int *buf;"                                                           +"\n"+
			            "	void func_GLOB(unsigned n)"                                          +"\n"+
			            "{"                                                                    +"\n"+
			            "	      		int aux;"                                                    +"\n"+
			            "	      		if (n == 1) {"                                               +"\n"+
			            "	          			buf = &aux; "                                           +"\n"+
			          
			            "	      		} else {"                                                       +"\n"+
			            "	          			buf = &aux; "                                           +"\n"+
			            "                        buf = (int *)malloc(n * sizeof(int));"        +"\n"+
			            "	          			buf = (int *)malloc(n * sizeof(int));"                  +"\n"+
			            "	      		}"                                                           +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "GLOB"
			            ,
			            },
		/////////////////  0   ///////////////////	
			            {
			          
			            "	int *buf;"                                                           +"\n"+
			            "	void func_GLOB(unsigned n)"                                          +"\n"+
			            "{"                                                                    +"\n"+
			            "	      		int aux;"                                                    +"\n"+
			            "	      		if (n == 1) {"                                               +"\n"+
			            "	          			buf = &aux;   //defect"                                 +"\n"+
			            "	      		} else {"                                                    +"\n"+
			            "	          			buf = (int *)malloc(n * sizeof(int));"                  +"\n"+
			            "	      		}"                                                           +"\n"+
			            "   while(1)"                                                          +"\n"+
			            "{   buf = &aux;"                                                      +"\n"+
			            "    buf = buf = (int *)malloc(n * sizeof(int));"                      +"\n"+
			            ""                                                                     +"\n"+
			            "}"                                                                    +"\n"+
			            "}"                                                                    
			            ,   
			            "gcc"
			            ,
			            "GLOB"
			            ,
			            },
		/////////////////  0   ///////////////////	
			            {
			            
			            "	int *buf;"                                                           +"\n"+
			            "	void func_GLOB(unsigned n)"                                          +"\n"+
			            "{"                                                                    +"\n"+
			            "	      		int aux;"                                                    +"\n"+
			            "                 buf = &aux; "                                        +"\n"+
			            "                if(n > 2)"                                            +"\n"+
			            "                 buf = &aux; "                                        +"\n"+
			            "	      		if (n == 1) {"                                               +"\n"+
			            "	          			buf = &aux;   //defect"                                 +"\n"+
			            "	      		} else if(n == 2){"                                          +"\n"+
			            "	          			buf = (int *)malloc(n * sizeof(int));"                  +"\n"+
			            "	      		}"                                                           +"\n"+
			            "                else "                                                +"\n"+
			            "               {"                                                     +"\n"+
			            "                    buf = &aux; "                                     +"\n"+
			            "               }"                                                     +"\n"+
			            ""                                                                     +"\n"+
			            "               "                                                      +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "GLOB"
			            },            
		
		 });
	 }
}

