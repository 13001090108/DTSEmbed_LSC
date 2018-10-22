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
public class CCW extends ModelTestBase{
	public CCW(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/CCW-0.1.xml";
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
		            "void fun0()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            " int i=-1;"                                                           +"\n"+
		            "  while(i<=0)//ok"                                                    +"\n"+
		            " {"                                                                   +"\n"+
		            "	i++;"                                                                +"\n"+
		            "}"                                                                    +"\n"+
		            "}"                                                                    
		            ,
		            "all"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  1   ///////////////////	
		            {
		            "void fun2()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "   int j=9;"                                                          +"\n"+
		            "   while(j==0)//ok"                                               +"\n"+
		            "   {"                                                                 +"\n"+
		            "      j--;"                                                           +"\n"+
		            "   }"                                                                 +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },

	/////////////////  2   ///////////////////	
		            {
		            "int fun1()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            " int i=-1;"                                                           +"\n"+
		            "  while(i<=0)//ok"                                                    +"\n"+
		            " {"                                                                   +"\n"+
		            "	i++;"                                                                +"\n"+
		            "	}"                                                                   +"\n"+
		            " return i;"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            "void main()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            " int k=5;"                                                            +"\n"+
		            " while(k= fun1())//defect"                                            +"\n"+
		            "  k--;"                                                               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "CCW"
		            ,
		            },

	/////////////////  3  ///////////////////	
		            {
		            "int fun1()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            " int i=-1;"                                                           +"\n"+
		            "  while(i<=0)//ok"                                                    +"\n"+
		            " {"                                                                   +"\n"+
		            "	i++;"                                                                +"\n"+
		            "	}"                                                                   +"\n"+
		            " return i;"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            "void main()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            " int k=5;"                                                            +"\n"+
		            " while(k>fun1())//defect"                                             +"\n"+
		            "  k--;"                                                               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  4   ///////////////////	
		            {
		            "int fun1()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            " int i=-1;"                                                           +"\n"+
		            "  while(0)//ok"                                                       +"\n"+
		            " {"                                                                   +"\n"+
		            "	i++;"                                                                +"\n"+
		            "}"                                                                    +"\n"+
		            " return i;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  5   ///////////////////	
		            {
		            "int fun1()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            " int i=-1;"                                                           +"\n"+
		            "  while(true)//ok"                                                    +"\n"+
		            " {"                                                                   +"\n"+
		            "	i++;"                                                                +"\n"+
		            "}"                                                                    +"\n"+
		            " return i;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  6   ///////////////////	
		            {
		            "int fun1()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            " int i=-1;"                                                           +"\n"+
		            "  while(1+2+3)//defect"                                               +"\n"+
		            " {"                                                                   +"\n"+
		            "	i++;"                                                                +"\n"+
		            "}"                                                                    +"\n"+
		            " return i;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "CCW"
		            ,
		            },
	/////////////////  7   ///////////////////	
		            {
		            "void fun1()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	int i=5;"                                                            +"\n"+
		            "    while(sizeof(int)==4)//defect"                                    +"\n"+
		            "     i++;"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "CCW"
		            ,
		            },
    /////////////////  8   ///////////////////	
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

//目前尚不能检测宏定义  如 define N 3; if(N>2)//defect 但是语法树中不包括define 语句 故有错;

	 
		 });
	 }
}

