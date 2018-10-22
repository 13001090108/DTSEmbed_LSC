package softtest.test.gcc.rules.rule;

import java.util.Arrays;
import java.util.Collection;
import java.util.Set;

import org.junit.BeforeClass;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import softtest.fsm.c.FSMLoader;
import softtest.fsm.c.FSMMachine;
import softtest.fsmanalysis.c.FSMAnalysisVisitor;
import softtest.interpro.c.InterContext;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.test.c.rules.ModelTestBase;

@RunWith(Parameterized.class)
public class RFIE extends ModelTestBase {
	public RFIE(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/rule/RFIE-0.1.xml";
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
	/////////////////  0   ///////////////////	
		            {
		            "unsigned int exp_1(unsigned int * p_1)"                               +"\n"+
		            "{"                                                                    +"\n"+
		            "  unsigned int x = *p_1;"                                             +"\n"+
		            "  (*p_1) = x*x;"                                                      +"\n"+
		            "  return (x)  ;"                                                      +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    +"\n"+
		            "unsigned int exp_2(unsigned int * p_1)"                               +"\n"+
		            "{"                                                                    +"\n"+
		            "  unsigned int x = *p_1;"                                             +"\n"+
		            "  (*p_1) = (x%2);"                                                    +"\n"+
		            "  return (x);"                                                        +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void static_p(void)"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "  unsigned int y=3u, x=0u;"                                           +"\n"+
		            "  x=exp_1(&y)+exp_2(&y);"                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "RFIE"
		            ,
		            },

		 });
	 }
}
