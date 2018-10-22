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
public class CCI extends ModelTestBase{
	public CCI(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/CCI-0.1.xml";
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
		            ""                                                                     +"\n"+
		            "void foo() {"                                                         +"\n"+
		            "	int i=0,x=0,y=1;"                                                    +"\n"+
		            "   if (sizeof(char) < 2)  // defect - the condition is constant"      +"\n"+
		            "   {"                                                                 +"\n"+
		            "    i =i+1;  	"                                                       +"\n"+
		            "   }"                                                                 +"\n"+
		            "   if(sizeof(char) ==1) //defect"                                     +"\n"+
		            "    i++;"                                                             +"\n"+
		            "   if(sizeof(int)+1+4 +x < y )"                                       +"\n"+
		            "	x++;"                                                                +"\n"+
		            "   if(3+2-34 >1) //defect"                                            +"\n"+
		            "   {"                                                                 +"\n"+
		            "     i= i-1;"                                                         +"\n"+
		            "   }"                                                                 +"\n"+
		            "  if(x>3)"                                                            +"\n"+
		            "	i++;"                                                                +"\n"+
		            "  if(x=2) //defect"                                                   +"\n"+
		            "   y++;"                                                              +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "CCI"
		            ,
		            },
    /////////////////  1   ///////////////////	
		            {
		            "void fun()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "  int i=0;"                                                           +"\n"+
		            "  int j=1;"                                                           +"\n"+
		            "  if((i=(j+3)) >= 8)"                                                 +"\n"+
		            "    i++;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  2   ///////////////////	
		            {
		            "void fun()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            " 	int i=0;"                                                           +"\n"+
		            "    int j=1;"                                                         +"\n"+
		            "     if(((i=3)+1)>1)"                                                 +"\n"+
		            "       i++;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },

	/////////////////  3   ///////////////////	
		            {
		            "int  fun()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "   return 1;"                                                         +"\n"+
		            "}"                                                                    +"\n"+
		            "void fun1()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	int k=0;"                                                            +"\n"+
		            "    if(k=fun())//defect"                                              +"\n"+
		            "      k++;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "CCI"
		            ,
		            },
	/////////////////  4   ///////////////////	
		            {
		            "void fun()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            " 	int i=0;"                                                           +"\n"+
		            "    int j=1;"                                                         +"\n"+
		            "     if(i=j+1)"                                                       +"\n"+
		            "       i++;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "CCI"
		            ,
		            },

//目前尚不能检测宏定义  如 define N 3; if(N>2)//defect 但是语法树中不包括define 语句 故有错;

	 
		 });
	 }
}

