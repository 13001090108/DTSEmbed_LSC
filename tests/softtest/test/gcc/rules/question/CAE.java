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
    /////////////////  0   ///////////////////	
		            {
		            "#define true 1"                                                       +"\n"+
		            "#define false 0"                                                      +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void f_CAE(_Bool b)"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "    //..."                                                            +"\n"+
		            "    if (b=false){// CAE,defect"                                       +"\n"+
		            "	    printf(\"false\");"                                                +"\n"+
		            "    }"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "CAE"
		            ,
		            },
    /////////////////  1   ///////////////////	
		            {
		            "void f_CAE_2()"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "    int i = 1;"                                                       +"\n"+
		            "    int j = 0;"                                                       +"\n"+
		            "    //..."                                                            +"\n"+
		            "    if(i = j){// CAE,defect"                                          +"\n"+
		            "        j++;"                                                         +"\n"+
		            "    }"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "CAE"
		            ,
		            },
    /////////////////  2  ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "int qq()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "    return 0;"                                                        +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f_CAE_3(int i)"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "    if(i = qq()){// CAE,defect"                                       +"\n"+
		            "        printf(\"OK\");"                                                +"\n"+
		            "    }"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "CAE"
		            ,
		            },

		            
				 
		 });
	 }
}


