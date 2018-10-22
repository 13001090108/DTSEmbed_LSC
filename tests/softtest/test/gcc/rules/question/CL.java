package softtest.test.gcc.rules.question;

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
public class CL extends ModelTestBase{
	public CL(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/CL-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("question");
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
		            "void fun()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "  int j=1, k=2,a=3,b =0;"                                                  +"\n"+
		            " for(j=1;j<a;j++)"                                                    +"\n"+
		            "  k++;"                                                               +"\n"+
		            " if(k<j)"                                                             +"\n"+
		            "    k += 1;  "                                                        +"\n"+
		            "  a = k>j;"                                                           +"\n"+
		            " while(a>o)"                                                          +"\n"+
		            "   j >=k; //defect"                                                   +"\n"+
		            " a<=b; //defect "                                                     +"\n"+
		            " switch(a>b)"                                                         +"\n"+
		            " {case 0: "                                                           +"\n"+
		            "     a++;"                                                            +"\n"+
		            "     break;"                                                          +"\n"+
		            "  case 1:"                                                            +"\n"+
		            "     b++;"                                                            +"\n"+
		            "     break;"                                                          +"\n"+
		            "  default:"                                                           +"\n"+
		            "     break;"                                                          +"\n"+
		            " }"                                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "CL"
		            ,
		            },
	/////////////////  1   ///////////////////	
		            {
		            "void fun1()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "  int a =0, b=1;"                                                     +"\n"+
		            "  if(a != b)"                                                         +"\n"+
		            "     a ++;"                                                           +"\n"+
		            "  else"                                                               +"\n"+
		            "     a ==b; //defect"                                                 +"\n"+
		            ""                                                                     +"\n"+
		            "  while(a==b)"                                                        +"\n"+
		            "   a= 1;"                                                             +"\n"+
		            "  a!=b; //defect"                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "CL"
		            ,
		            },
	/////////////////  2  ///////////////////	
		            {
		            "void fun2()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	int a=1,b=1,c=0,d=1;"                                                +"\n"+
		            "	a = !b;"                                                             +"\n"+
		            "    if(a && b)"                                                       +"\n"+
		            "        a || b; //defect"                                             +"\n"+
		            "    else "                                                            +"\n"+
		            "        c & d; //defect"                                              +"\n"+
		            "    if(c & d)"                                                        +"\n"+
		            "        a =0;"                                                        +"\n"+
		            "    while (c | d)"                                                    +"\n"+
		            "      c++;"                                                           +"\n"+
		            "    !a; //defect"                                                     +"\n"+
		            "    if(!b)"                                                           +"\n"+
		            "    c | d; //defect"                                                  +"\n"+
		            "    switch(a&&b)"                                                     +"\n"+
		            "    {"                                                                +"\n"+
		            "	   case 0:"                                                          +"\n"+
		            "         a&&b; //defect"                                              +"\n"+
		            "         break;"                                                      +"\n"+
		            "       case 1:"                                                       +"\n"+
		            "         a || b; //defect"                                            +"\n"+
		            "         break;"                                                      +"\n"+
		            "       default:"                                                      +"\n"+
		            "          break;"                                                     +"\n"+
		            "	"                                                                    +"\n"+
		            "    }"                                                                +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "CL"
		            ,
		            },




	 
		 });
	 }
}

