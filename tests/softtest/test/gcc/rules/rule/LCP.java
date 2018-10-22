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
public class LCP extends ModelTestBase {
	public LCP(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/rule/LCP-0.1.xml";
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
		            "void func(int* p, int *q) {"                                          +"\n"+
		            "  if(p > q)  ;"                                                       +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "LCP"
		            ,
		            },
		/////////////////  1   ///////////////////	
		            {
		            "void func(int* p, int *q) {"                                          +"\n"+
		            "  if(p < q)  ;"                                                       +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "LCP"
		            ,
		            },
		/////////////////  2   ///////////////////	
		            {
		            "void func(int* p, int *q) {"                                          +"\n"+
		            "  if(p == q)  ;"                                                      +"\n"+
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
