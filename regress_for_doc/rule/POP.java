package rule;

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
public class POP extends ModelTestBase{
	public POP(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/rule/POP-0.1.xml";
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
	/////////////////  1   ///////////////////	
		            {
		            "    unsigned int static_p(p_1)"                                       +"\n"+
		            "    {"                                                                +"\n"+
		            "       unsigned int result;"                                          +"\n"+
		            "   "                                                                  +"\n"+
		            "        result=p_1 *2;"                                               +"\n"+
		            "        return result;"                                               +"\n"+
		            "    }"                                                                
		            ,
		            "gcc"
		            ,
		            "POP"
		            ,
		            },	
	/////////////////  2   ///////////////////	
		            {
		            "struct s_type_b{unsigned int xs;};    "                               +"\n"+
		            "void static_p_a(unsigned int p_1,struct s_type_b *);"                 +"\n"+
		            "void static_p_a(unsigned int p_1,struct s_type_b *)"                  +"\n"+
		            "{"                                                                    +"\n"+
		            "       /*...*/"                                                       +"\n"+
		            " }"                                                                   
		            ,
		            "gcc"
		            ,
		            "POP"
		            ,
		            },	
	/////////////////  3   ///////////////////	
		            {
		            " void satic_p()"                                                      +"\n"+
		            "   {"                                                                 +"\n"+
		            "       /*...*/"                                                       +"\n"+
		            "   }"                                                                 
		            ,
		            "gcc"
		            ,
		            "POP"
		            ,
		            },
	/////////////////  4   ///////////////////	
		            {
		            "float static_p(unsigned int,  unsigned short p_2);"                   
			            ,
			            "gcc"
			            ,
			            "POP"
			            ,
			            },
		 });
	 }
}

