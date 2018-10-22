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
public class VVAP extends ModelTestBase {
	public VVAP(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/rule/VVAP-0.1.xml";
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
		            "void void_para_func(void* p_1)"                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "  /*...*/"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            "void static_p(unsigned int p_1, unsigned int p_2)"                    +"\n"+
		            "{"                                                                    +"\n"+
		            "  int y=0;"                                                           +"\n"+
		            "  void *v_ptr=&y;"                                                    +"\n"+
		            "  y=(int)(p_1+p_2);"                                                  +"\n"+
		            "  void_para_func(v_ptr);"                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "VVAP"
		            ,
		            },

		 });
	 }
}
