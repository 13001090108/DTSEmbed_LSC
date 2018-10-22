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
public class FPA2 extends ModelTestBase {
	public FPA2(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/rule/FPA2-0.1.xml";
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
			            "int static_p(float up_1);"                                            +"\n"+
			            "int static_p(unsigned int up_1)"                                      +"\n"+
			            "{"                                                                    +"\n"+
			            "  int ret=0;"                                                         +"\n"+
			            "  /*...*/"                                                            +"\n"+
			            "  return ret;"                                                        +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "FPA2"
			            ,
			            },
		/////////////////  1   ///////////////////	
		            {
		            "float static_p(unsigned int, unsigned short);"                        +"\n"+
		            "unsigned int static_p(unsigned int p_1, unsigned short p_2)"          +"\n"+
		            "{"                                                                    +"\n"+
		            "  unsigned int result=0;"                                             +"\n"+
		            "  /*...*/"                                                            +"\n"+
		            "  return result;"                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "FPA2"
		            ,
		            },
		/////////////////  2   ///////////////////	
		            {
		            "int static_p(int, char);"                                            +"\n"+
		            "int static_p(int up_1, int up_2)"                                      +"\n"+
		            "{"                                                                    +"\n"+
		            "  int ret=0;"                                                         +"\n"+
		            "  /*...*/"                                                            +"\n"+
		            "  return ret;"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "FPA2"
		            ,
		            },
		 });
	 }
}
