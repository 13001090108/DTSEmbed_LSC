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
public class StaticTest extends ModelTestBase{
	public StaticTest(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/StaticTest-0.1.xml";
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
		            "static int  c;"                                                       +"\n"+
		            "void fun1()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "  c=1;"                                                               +"\n"+
		            "}"                                                                    +"\n"+
		            "void func()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "  int a=1;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "StaticTest"
		            ,
		            },
	/////////////////  1   ///////////////////	
	/////////////////  0   ///////////////////	
		            {
		            "static int  c;"                                                       +"\n"+
		            "void fun1()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "  c=1;"                                                               +"\n"+
		            "   c++;"                                                              +"\n"+
		            "}"                                                                    +"\n"+
		            "void func()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "  int a=1;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "StaticTest"
		            ,
		            },
	/////////////////  0   ///////////////////	
		            {
		            "static int  c;"                                                       +"\n"+
		            "void fun1()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "  c=1;"                                                               +"\n"+
		            "   c++;"                                                              +"\n"+
		            "}"                                                                    +"\n"+
		            "void func()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "  int a=1;"                                                           +"\n"+
		            "   c++;"                                                              +"\n"+
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

