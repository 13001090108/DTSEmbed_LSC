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
public class NUEBI extends ModelTestBase {
	public NUEBI(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/rule/NUEBI-0.1.xml";
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
		            "void dosth(void);"                                                    +"\n"+
		            "void doother(void); "                                                 +"\n"+
		            ""                                                                     +"\n"+
		            "void func() {"                                                        +"\n"+
		            "  int a = 1;"                                                         +"\n"+
		            "  if(a > 0)"                                                          +"\n"+
		            "  dosth();"                                                           +"\n"+
		            "  else  if(a==0)"                                                     +"\n"+
		            "  doother();  "                                                       +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		/////////////////  1   ///////////////////	
		            {
		            "void doA(void);"                                                      +"\n"+
		            "void doB(void); "                                                     +"\n"+
		            "void doC(void); "                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "void func() {"                                                        +"\n"+
		            "  int a = 1;"                                                         +"\n"+
		            "  if(a > 0)"                                                          +"\n"+
		            "    doA();"                                                           +"\n"+
		            "  if(a==0)"                                                     +"\n"+
		            "    doB();"                                                           +"\n"+
		            "  else"                                                               +"\n"+
		            "    doC(); "                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NUEBI"
		            ,
		            },
		 });
	 }
}
