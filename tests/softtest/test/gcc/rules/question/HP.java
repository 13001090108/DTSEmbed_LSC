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
public class HP extends ModelTestBase{
	public HP(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/HP-0.1.xml";
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
		            "void foo(int a,int b) {"                                              +"\n"+
		            "	int a = 0; "                                                         +"\n"+
		            "    char b ='a';    "                                                 +"\n"+
		            "	a++;"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "HP"
		            ,
		            },
	/////////////////  0   ///////////////////	
		            {
		            "void fun(int *p)"                                                     +"\n"+
		            "{"                                                                    +"\n"+
		            "  int *p;"                                                            +"\n"+
		            "   p=null;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "HP"
		            ,
		            },

	/////////////////  0   ///////////////////	
		            {
		            "int fun(int a)"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "  return a;"                                                          +"\n"+
		            "}"                                                                    +"\n"+
		            "void fun1(int a)"                                                     +"\n"+
		            "{"                                                                    +"\n"+
		            "   int i=fun1(a);"                                                    +"\n"+
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

