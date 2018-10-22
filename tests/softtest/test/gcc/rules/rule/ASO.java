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
public class ASO extends ModelTestBase {
	public ASO(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/rule/ASO-0.1.xml";
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
		            "void static_p(void)"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "  unsigned int x=1u;"                                                 +"\n"+
		            "  unsigned int y=2u;"                                                 +"\n"+
		            "  unsigned int z=3u;"                                                 +"\n"+
		            "  /*...*/"                                                            +"\n"+
		            "  x+=1;"                                                              +"\n"+
		            "  z+=y;"                                                              +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "ASO"
		            ,
		            },
		        	/////////////////  1   ///////////////////	
		            {
		            "void static_p(void)"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "  unsigned int x=1u;"                                                 +"\n"+
		            "  unsigned int y=2u;"                                                 +"\n"+
		            "  unsigned int z=3u;"                                                 +"\n"+
		            "  /*...*/"                                                            +"\n"+
		            "  z-=y;"                                                              +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "ASO"
		            ,
		            },
		            /////////////////  2   ///////////////////	
		            {
		            "void foo(unsigned int p_x){}"                                         +"\n"+
		            "void static_p(void)"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "  unsigned int x=1u;"                                                 +"\n"+
		            "  unsigned int y=2u;"                                                 +"\n"+
		            "  foo(x++);"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "ASO"
		            ,
		            },
		            /////////////////  3   ///////////////////	
		            {
		            "void foo(unsigned int p_x){}"                                         +"\n"+
		            "void static_p(void)"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "  unsigned int x=1u;"                                                 +"\n"+
		            "  unsigned int y=2u;"                                                 +"\n"+
		            "  /*...*/"                                                            +"\n"+
		            "  x=x+y++;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "ASO"
		            ,
		            },
		            /////////////////  4   ///////////////////	
		            {
		            "void foo(unsigned int p_x){}"                                         +"\n"+
		            "void static_p(void)"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "  unsigned int x=1u;"                                                 +"\n"+
		            "  unsigned int y=2u;"                                                 +"\n"+
		            "  int flag=0;"                                                        +"\n"+
		            "  /*...*/"                                                            +"\n"+
		            "  if(flag==0)"                                                        +"\n"+
		            "  {"                                                                  +"\n"+
		            "    x++;"                                                             +"\n"+
		            "  }"                                                                  +"\n"+
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
