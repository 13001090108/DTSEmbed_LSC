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
public class RLVAP extends ModelTestBase{
	public RLVAP(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/RLVAP-0.1.xml";
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
		            "#include <stdio.h>"                                                   +"\n"+
		            "#define OK 1"                                                         +"\n"+
		            "int a;"                                                               +"\n"+
		            "int* f_RLVAP_1 ()"                                                    +"\n"+
		            "{"                                                                    +"\n"+
		            "     int i=a;"                                                        +"\n"+
		            "     return &i;//RLVAP"                                               +"\n"+
		            "}"                                                                    +"\n"+
		            "void f_RLVAP_main ()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "     int *p = f_RLVAP_1 ();"                                          +"\n"+
		            "     *p = 0xbb;"                                                      +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "RLVAP"
		            ,
		            },				 
	/////////////////  1   ///////////////////	
		            {
		            "int* f_RLVAP_2 ()"                                                    +"\n"+
		            "{"                                                                    +"\n"+
		            "     int i=0;"                                                        +"\n"+
		            "     int *p=&i;//RLVAP"                                               +"\n"+
		            "     return p;"                                                       +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "RLVAP"
		            ,
		            },	
	/////////////////  0   ///////////////////	
		            {
		                "int t ;"                                                              +"\n"+
		                ""                                                                     +"\n"+
		                ""                                                                     +"\n"+
		                "int *f()"                                                             +"\n"+
		                "{"                                                                    +"\n"+
		                ""                                                                     +"\n"+
		                "   int i;"                                                            +"\n"+
		                "   int *p ;"                                                        +"\n"+
		                    "p= &t;"                                                      +"\n"+
		                "   p = &i;"                                                      +"\n"+
		                "   "                                                                  +"\n"+
		                "  return p;"                                                          +"\n"+
		                "}"                                                                     
		                ,
			            "gcc"
			            ,
		                "RLVAP"
		                ,
		            },	
	
	/////////////////  0   ///////////////////	
		            {
		            "int *fun()"                                                           +"\n"+
		            ""                                                                     +"\n"+
		            "{"                                                                    +"\n"+
		            "    int i = 1;"                                                       +"\n"+
		            "   int* p = (int *) malloc ( sizeof(int) );"                          +"\n"+
		            "   "                                                                  +"\n"+
		            "    free(p);"                                                         +"\n"+
		            ""                                                                     +"\n"+
		            "  return p;"                                                          +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		    
		           
		            "RLVAP"
		            ,
		            },
	/////////////////  0   ///////////////////	
		            {
		            "int *fun()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "  int * p;"                                                           +"\n"+
		            "  int * i;"                                                           +"\n"+
		            "  i = (int*)malloc(sizeof(int));"                                     +"\n"+
		            "  p = i;"                                                             +"\n"+
		            "  free(i);"                                                           +"\n"+
		            "  return p;"                                                          +"\n"+
		            ""                                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            
		            "RLVAP"
		            ,
		            },
		        /////////////////  0   ///////////////////	
		            {
		            "int *fun()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "  int * p;"                                                           +"\n"+
		            "  int * i;"                                                           +"\n"+
		            "  i = (int*)malloc(sizeof(int));"                                     +"\n"+
		            "  p = i;"                                                             +"\n"+
		            "  free(i);"                                                           +"\n"+
		            "  return NULL;"                                                          +"\n"+
		            ""                                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            
		            "OK"
		            ,
		            },
	/////////////////  0   ///////////////////	
		            {
		            "int* zk_rlvap_3_f1()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	int* ptr = (int*)malloc(2);"                                         +"\n"+
		            ""                                                                     +"\n"+
		            "	if (ptr)"                                                            +"\n"+
		            "		return ptr; //FP"                                                   +"\n"+
		            "	else"                                                                +"\n"+
		            "		return NULL; //FP"                                                  +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int* zk_rlvap_3_f2()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	int* ptr = (int*)malloc(2);"                                         +"\n"+
		            ""                                                                     +"\n"+
		            "	if (ptr)"                                                            +"\n"+
		            "	{"                                                                   +"\n"+
		            "		free(ptr);"                                                         +"\n"+
		            "		return ptr; //DEFECT"                                               +"\n"+
		            "	}"                                                                   +"\n"+
		            "	else"                                                                +"\n"+
		            "		return NULL; //FP"                                                  +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "RLVAP"
		            
		            ,
		            },


				 
		 });
	 }
}

