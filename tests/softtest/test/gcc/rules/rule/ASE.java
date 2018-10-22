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
public class ASE extends ModelTestBase {
	public ASE(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/rule/ASE-0.1.xml";
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
		            "void static_p(int p_1)"                                               +"\n"+
		            "{"                                                                    +"\n"+
		            "  int i=p_1;"                                                         +"\n"+
		            "  int x=0;"                                                           +"\n"+
		            "  /*...*/"                                                            +"\n"+
		            "  while(i!=0){"                                                       +"\n"+
		            "    i--;"                                                             +"\n"+
		            "    if(x==0){"                                                        +"\n"+
		            "      continue;"                                                      +"\n"+
		            "    }"                                                                +"\n"+
		            "  }"                                                                  +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "ASE"
		            ,
		            },
		            /////////////////  1   ///////////////////	
		            {
		            "void foo(unsigned int p_1)"                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "  /*...*/"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void static_p(unsigned int p_1)"                                      +"\n"+
		            "{"                                                                    +"\n"+
		            "  static unsigned int type0=0u;"                                      +"\n"+
		            "  static unsigned int type1=1u;"                                      +"\n"+
		            "  /*...*/"                                                            +"\n"+
		            "  (p_1==0)?foo(type0): foo(type1);"                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "ASE"
		            ,
		            },
		            /////////////////  2   ///////////////////	
		            {
		            "void static_p(unsigned int p_1)"                                      +"\n"+
		            "{"                                                                    +"\n"+
		            "  unsigned int x=0u;"                                                 +"\n"+
		            "  x;"                                                                 +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "ASE"
		            ,
		            },
		            /////////////////  3   ///////////////////	
		            {
		            "void static_p(void)"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "  unsigned int Time_Loop=100u;"                                       +"\n"+
		            "  Time_Loop--;;"                                                      +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "ASE"
		            ,
		            },

		 });
	 }
}
