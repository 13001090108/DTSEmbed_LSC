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
public class CCS extends ModelTestBase{
	public CCS(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/CCS-0.1.xml";
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
		            "	int i=1;"                                                            +"\n"+
		            "    switch(1+2)//defect"                                              +"\n"+
		            "	{"                                                                   +"\n"+
		            "		case 0:"                                                            +"\n"+
		            "            i++;"                                                     +"\n"+
		            "            break;"                                                   +"\n"+
		            "        case 1:"                                                      +"\n"+
		            "            i--;"                                                     +"\n"+
		            "            break;"                                                   +"\n"+
		            "        default:"                                                     +"\n"+
		            "            break;"                                                   +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "CCS"
		            ,
		            },
	/////////////////  1   ///////////////////	
		            {
		            "void fun0()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	int i=1;"                                                            +"\n"+
		            "    switch(sizeof(char) ==9 )//defect"                                +"\n"+
		            "	{"                                                                   +"\n"+
		            "		case 0:"                                                            +"\n"+
		            "            i++;"                                                     +"\n"+
		            "            break;"                                                   +"\n"+
		            "        case 1:"                                                      +"\n"+
		            "            i--;"                                                     +"\n"+
		            "            break;"                                                   +"\n"+
		            "        default:"                                                     +"\n"+
		            "            break;"                                                   +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "CCS"
		            ,
		            },

	/////////////////  2   ///////////////////	
		            {
		            "void fun1() {"                                                        +"\n"+
		            "    "                                                                 +"\n"+
		            "  int i=0;"                                                           +"\n"+
		            "  switch(i)"                                                          +"\n"+
		            "  {"                                                                  +"\n"+
		            "     case 0:"                                                         +"\n"+
		            "          i++;"                                                       +"\n"+
		            "          break;"                                                     +"\n"+
		            "     default:"                                                        +"\n"+
		            "          break;"                                                     +"\n"+
		            "  }"                                                                  +"\n"+
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
     		           "  switch(i=3)"                                                          +"\n"+
	   		            "  {"                                                                  +"\n"+
	   		            "     case 0:"                                                         +"\n"+
	   		            "          i++;"                                                       +"\n"+
	   		            "          break;"                                                     +"\n"+
	   		            "     default:"                                                        +"\n"+
	   		            "          break;"                                                     +"\n"+
	   		            "  }"                                                                  +"\n"+
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

