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
public class SN extends ModelTestBase {
	public SN(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/rule/SN-0.1.xml";
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
		            "unsigned int Fire_Command;"                                           +"\n"+
		            "void static_p(void)"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "  unsigned int Fire_Command=2u;"                                      +"\n"+
		            "}"
		            ,
		            "gcc"
		            ,
		            "SN"
		            ,
		            },
		/////////////////  1   ///////////////////	
		            {
		            "unsigned int global_int=0;"                                           +"\n"+
		            "void static_p(unsigned int *global_int)"                              +"\n"+
		            "{"                                                                    +"\n"+
		            "  /*...*/"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "SN"
		            ,
		            },
		 });
	 }
}
