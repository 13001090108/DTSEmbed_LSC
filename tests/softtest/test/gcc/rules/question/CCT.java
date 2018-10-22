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
public class CCT extends ModelTestBase{
	public CCT(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/CCT-0.1.xml";
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
		            "void fun0(int a, int b) {"                                            +"\n"+
		            "  int x = (sizeof(int) == 4) ? a : b;   "                             +"\n"+
		            "// defect - the condition is constant "                               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "CCT"
		            ,
		            },
	/////////////////  1   ///////////////////	
		            {
		            ""                                                                     +"\n"+
		            "void fun1()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	int i=0;"                                                            +"\n"+
		            "    int a=4,b=5;"                                                     +"\n"+
		            "    i=(a>3?a:b);"                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  2   ///////////////////	
		            {
		            ""                                                                     +"\n"+
		            "void fun2()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "   int i=1;"                                                          +"\n"+
		            "   i= (2+2? 2:4);//defect"                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "CCT"
		            ,
		            },
	/////////////////  3   ///////////////////	
		            {
		            ""                                                                     +"\n"+
		            "int fun3()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "  int k=0;"                                                           +"\n"+
		            "  return 2>1? k:1; //defect"                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "CCT"
		            ,
		            },
		        	/////////////////  3   ///////////////////	
		            {
		            ""                                                                     +"\n"+
		            "int fun3()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "  int k=0;"                                                           +"\n"+
		            "  return k? k:1; //defect"                                          +"\n"+
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

