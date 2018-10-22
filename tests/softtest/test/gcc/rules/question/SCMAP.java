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
public class SCMAP extends ModelTestBase{
	public SCMAP(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/SCMAP-0.1.xml";
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
		            "typedef struct S_1{"                                                  +"\n"+
		            "     int a,b,c;"                                                      +"\n"+
		            "}tS, *pS;"                                                            +"\n"+
		            ""                                                                     +"\n"+
		            "void f_SCMAP_1(int n) {"                                              +"\n"+
		            "     pS tmp1 = (pS) malloc(n * sizeof(pS));"                          +"\n"+
		            "     free(tmp1);"                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "SCMAP"
		            ,
		            },				 
	/////////////////  1   ///////////////////	
		            {
		            "typedef struct S_2{"                                                  +"\n"+
		            "     int a,b;"                                                        +"\n"+
		            "     char c;"                                                         +"\n"+
		            "}tS, *pS;"                                                            +"\n"+
		            ""                                                                     +"\n"+
		            "void f_SCMAP_2(int n) {"                                              +"\n"+
		            "     pS tmp1 = (pS) malloc(4);"                                       +"\n"+
		            "     //..."                                                           +"\n"+
		            "     tmp1 = (pS) realloc(tmp1,n * sizeof(pS));//SCMAP"                +"\n"+
		            "     free(tmp1);"                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "SCMAP"
		            ,
		            },		         
	/////////////////  2   ///////////////////	
		            {
		            "typedef struct S_3{"                                                  +"\n"+
		            "     int a,b,c;"                                                      +"\n"+
		            "}tS, *pS;"                                                            +"\n"+
		            ""                                                                     +"\n"+
		            "void f_SCMAP_3(int n) {"                                              +"\n"+
		            "     pS tmp1 = (pS) calloc(n, sizeof(pS));//SCMAP"                    +"\n"+
		            "     free(tmp1);"                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "SCMAP"
		            ,
		            },
   
		            
				 
		 });
	 }
}

