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
		            "void f_FDT_1(int i) {"                                                +"\n"+
		            "    char c;"                                                          +"\n"+
		            "    c = i;// FDT,defect"                                              +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "FDT"
		            ,
		            },
    /////////////////  1   ///////////////////	
		            {
		            "#include \"stdio.h\""                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void f_FDT_2()"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "	int n;"                                                              +"\n"+
		            "	scanf( \"%c\", &n );//FDT,defect"                                      +"\n"+
		            "	printf(\"the n is %d\", n);//FDT,defect"                               +"\n"+
		            "    return;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "FDT"
		            ,
		            },

				 
				 
		 });
	 }
}

