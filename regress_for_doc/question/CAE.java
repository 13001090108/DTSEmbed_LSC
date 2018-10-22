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
public class CAE extends ModelTestBase{
	public CAE(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/CAE-0.1.xml";
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
		            "#include<stdbool.h>"                                                  +"\n"+
		            "	void f()"                                                            +"\n"+
		            "	{"                                                                   +"\n"+
		            "		bool b;"                                                            +"\n"+
		            "	    if (b=false){ "                                                  +"\n"+
		            "		       b=true;"                                                     +"\n"+
		            "	    }"                                                               +"\n"+
		            "	}"                                                                   
		            ,
		            "gcc"
		            ,
		            "CAE"
		            ,
		            },
				 
	/////////////////  2   ///////////////////	
		            {
		            ""                                                                     +"\n"+
		            "	void foo()"                                                          +"\n"+
		            "	{"                                                                   +"\n"+
		            "	  int i = 1;"                                                        +"\n"+
		            "	  int j = 0;"                                                        +"\n"+
		            "	  if(i = j)j++;"                                                     +"\n"+
		            "	}"                                                                   
		            ,
		            "gcc"
		            ,
		            "CAE"
		            ,
		            },
			 
	/////////////////  3   ///////////////////	
		            {
		            ""                                                                     +"\n"+
		            "	  int qq()"                                                          +"\n"+
		            "	{}"                                                                  +"\n"+
		            "	void foo(int i)"                                                     +"\n"+
		            "	{"                                                                   +"\n"+
		            "	  if(i=qq()){}"                                                      +"\n"+
		            "	}"                                                                   
		            ,
		            "gcc"
		            ,
		            "CAE"
		            ,
		            },
	            
				 
		 });
	 }
}



