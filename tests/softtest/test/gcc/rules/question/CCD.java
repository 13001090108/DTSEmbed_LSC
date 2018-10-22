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
public class CCD extends ModelTestBase{
	public CCD(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/CCD-0.1.xml";
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
		            "void foo() {"                                                         +"\n"+
		            "    int x = 3; "                                                      +"\n"+
		            "    while(x>0)"                                                       +"\n"+
		            "   x++;"                                                              +"\n"+
		            "    do {"                                                             +"\n"+
		            "      	x++;"                                                          +"\n"+
		            "    } while (x = 10);// defect - the condition is constant"           +"\n"+
		            "    do {"                                                             +"\n"+
		            "      	x--;"                                                          +"\n"+
		            "    } while (0);// Ok - typical usage of 'do' construct when a user wants to //organize a code block     "+"\n"+
		            "    do {"                                                             +"\n"+
		            "     	return;"                                                        +"\n"+
		            "    } while (true);// Ok - typical usage of 'do' construct when a user wants to //organize a infinite loop     "+"\n"+
		            "	do"                                                                  +"\n"+
		            "    {"                                                                +"\n"+
		            "       x =x+3;"                                                       +"\n"+
		            "    }while(x>0);"                                                     +"\n"+
		            "    do"                                                               +"\n"+
		            "    {"                                                                +"\n"+
		            " 		x=x+5;"                                                            +"\n"+
		            "    }while(3+2+1);//defect"                                           +"\n"+
		            "    do"                                                               +"\n"+
		            "	{"                                                                   +"\n"+
		            "      x=x-2;"                                                         +"\n"+
		            "	}while(sizeof(int)+x<5);"                                            +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "CCD"
		            ,
		            },
	/////////////////  0   ///////////////////	
		            {
		            "void fun()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "  int i=0;"                                                           +"\n"+
		            "  int j=1;"                                                           +"\n"+
		            "  while((i=(j+3)) != 8)"                                              +"\n"+
		            "    i++;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  0   ///////////////////	
		            {
		            "int fun()"                                                            +"\n"+
		            "{   int i=0;"                                                         +"\n"+
		            "		do { "                                                              +"\n"+
		            "	  if (i) i=0; "                                                      +"\n"+
		            "	} while (0);"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },

//目前尚不能检测宏定义  如 define N 3; if(N>2)//defect 但是语法树中不包括define 语句 故有错;

	 
		 });
	 }
}

