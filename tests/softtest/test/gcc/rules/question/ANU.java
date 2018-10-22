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
public class ANU extends ModelTestBase{
	public ANU(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/ANU-0.1.xml";
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
		            "void f_ANU_1(){"                                                      +"\n"+
		            "    //..."                                                            +"\n"+
		            "    int var;//ANU,var,defect"                                         +"\n"+
		            "    //..."                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "ANU"
		            ,
		            },
    /////////////////  1   ///////////////////	
		            {
		            "void f_ANU_2(int c)"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "    int i;//ANU,i,defect"                                             +"\n"+
		            "    while(c>0){"                                                      +"\n"+
		            "        i=c;"                                                         +"\n"+
		            "        break;"                                                       +"\n"+
		            "    }"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "ANU"
		            ,
		            },
	/////////////////  2   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void f_ANU_3(int n)"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "     int m=0;"                                                        +"\n"+
		            "     int i=0;"                                                        +"\n"+
		            "     for(i=0;i<10;i++)"                                               +"\n"+
		            "     {"                                                               +"\n"+
		            "         if(m==n)"                                                    +"\n"+
		            "         {"                                                           +"\n"+
		            "             printf(\"Equal.\");"                                       +"\n"+
		            "         }"                                                           +"\n"+
		            "         else"                                                        +"\n"+
		            "         {"                                                           +"\n"+
		            "             printf(\"Inequal.\");"                                     +"\n"+
		            "         }"                                                           +"\n"+
		            "         m=n;//ANU,m,false alarm"                                     +"\n"+
		            "     }"                                                               +"\n"+
		            "     system(\"pause\");"                                                +"\n"+
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

		

