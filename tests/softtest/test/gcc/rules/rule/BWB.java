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
public class BWB extends ModelTestBase {
	public BWB(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/rule/BWB-0.1.xml";
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
		            "int f(int i)"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "    if(i>0)"                                                          +"\n"+
		            "       i--;"                                                          +"\n"+
		            "    return i;"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BWB"
		            ,
		            },
		/////////////////  1   ///////////////////	
		            {
		            "int static_p (int p_1)"                                               +"\n"+
		            "{"                                                                    +"\n"+
		            "    int j=10;"                                                        +"\n"+
		            "    int k=0;"                                                         +"\n"+
		            "    /*...*/"                                                          +"\n"+
		            "    for(k=0; k<10; k=k+1) j--;"                                       +"\n"+
		            "    return j;"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BWB"
		            ,
		            },
		/////////////////  2   ///////////////////	
		            {
		            "int static_p(int p_1, int p_2)"                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "    int i=1;"                                                         +"\n"+
		            "    int j=2;"                                                         +"\n"+
		            "    /*...*/"                                                          +"\n"+
		            "    if(p_1>0){"                                                       +"\n"+
		            "        i=i-1;"                                                       +"\n"+
		            "    }else"                                                            +"\n"+
		            "        i=i+1;"                                                       +"\n"+
		            "    if(p_2>0){"                                                       +"\n"+
		            "        j=j+p_2;"                                                     +"\n"+
		            "    }else if (p_2<0){"                                                +"\n"+
		            "        j=j-p_2;"                                                     +"\n"+
		            "    }else{"                                                           +"\n"+
		            "        j=i ;"                                                        +"\n"+
		            "    }"                                                                +"\n"+
		            "    return i;"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BWB"
		            ,
		            },
		/////////////////  3   ///////////////////	
		            {
		            "void main (void)"                                                     +"\n"+
		            "{"                                                                    +"\n"+
		            "  /*...*/"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BWB"
		            ,
		            },
		/////////////////  4   ///////////////////	
		            {
		            "int main(void)"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "    /*...*/"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		/////////////////  5   ///////////////////	
		            {
		            "int main (int,  char*[])"                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "    /*...*/"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		/////////////////  6   ///////////////////	
		            {
		            "int f (int x, int y, int z)"                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "    if(x>0){"                                                         +"\n"+
		            "      x=x+1;"                                                         +"\n"+
		            "    }else if(x<0){"                                                   +"\n"+
		            "      x=x-2;"                                                         +"\n"+
		            "    }else{"                                                           +"\n"+
		            "      if(y>0){"                                                       +"\n"+
		            "        x=y+2;"                                                       +"\n"+
		            "      }else"                                                          +"\n"+
		            "        x=y-3;"                                                       +"\n"+
		            "      if(z>x){"                                                       +"\n"+
		            "        x++;"                                                         +"\n"+
		            "      }        "                                                      +"\n"+
		            "    }"                                                                +"\n"+
		            "    return x;"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BWB"
		            ,
		            },
	/////////////////  7   ///////////////////	
		            {
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "    int i=10;"                                                        +"\n"+
		            "    do{"                                                              +"\n"+
		            "        i--;     "                                                    +"\n"+
		            "    }while(i>0);"                                                     +"\n"+
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
