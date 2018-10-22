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
public class RS extends ModelTestBase{
	public RS(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/RS-0.1.xml";
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
		            "void f(int i)"                                                        +"\n"+
		            "  {"                                                                  +"\n"+
		            "  	switch (i){"                                                       +"\n"+
		            "  	case 1:"                                                           +"\n"+
		            "  		cout<<\"hello\"<<endl;"                                             +"\n"+
		            "  		break;"                                                           +"\n"+
		            "  		cout<<\"never\"<<endl;"                                             +"\n"+
		            "  	}"                                                                 +"\n"+
		            "  }"                                                                  
		            ,
		            "gcc"
		            ,
		            "RS"
		            ,
		            },

	/////////////////  2   ///////////////////	
		            {
		            "#define NULL 0"                                                       +"\n"+
		            ""                                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "        int foo(int c)"                                               +"\n"+
		            "       {"                                                             +"\n"+
		            "          int i = 5;"                                                 +"\n"+
		            "          if(c){"                                                     +"\n"+
		            "                return i;"                                            +"\n"+
		            "           }else{"                                                    +"\n"+
		            "                return --i;"                                          +"\n"+
		            "           }"                                                         +"\n"+
		            "      return i;"                                                      +"\n"+
		            "    }"                                                                
		            ,
		            "gcc"
		            ,
		            "RS"
		            ,
		            },
	            
	/////////////////  3   ///////////////////	
		            {
		            "  	int foo(int v)"                                                    +"\n"+
		            "  	{"                                                                 +"\n"+
		            "  	  int i=5;"                                                        +"\n"+
		            "  	  if(v){"                                                          +"\n"+
		            "  	    return 10;"                                                    +"\n"+
		            "  	  }else{"                                                          +"\n"+
		            "  	    return v;"                                                     +"\n"+
		            "  	  }"                                                               +"\n"+
		            "  	  i=v;"                                                            +"\n"+
		            "  	}"                                                                 
		            ,
		            "gcc"
		            ,
		            "RS"
		            ,
		            },
	            
				 
		 });
	 }
}


