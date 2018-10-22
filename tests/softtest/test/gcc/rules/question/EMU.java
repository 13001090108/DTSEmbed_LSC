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
public class EMU extends ModelTestBase{
	public EMU(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/EMU-0.1.xml";
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
		            "#include<stdio.h>"                                                    +"\n"+
		            "typedef enum Q1{Q1Send, Q1Recv} Q1;"                                  +"\n"+
		            "typedef enum Q2{Q2None, Q2Send, Q2Recv} Q2;"                          +"\n"+
		            "void f(){"                                                            +"\n"+
		            "     printf(\"A\");"                                                    +"\n"+
		            "}"                                                                    +"\n"+
		            "void g(){"                                                            +"\n"+
		            "     printf(\"B\");"                                                    +"\n"+
		            "}"                                                                    +"\n"+
		            "void f_EMU_1(Q1 q){"                                                  +"\n"+
		            "     switch (q){"                                                     +"\n"+
		            "          case Q2Send: f(); break;"                                   +"\n"+
		            "          case Q2Recv: g(); break;"                                   +"\n"+
		            "     }"                                                               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "EMU"
		            ,
		            },
	/////////////////  1   ///////////////////	
		            {
		            "#include<stdio.h>"                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "typedef enum Q1{Q1Send, Q1Recv} Q1;"                                  +"\n"+
		            "typedef enum Q2{Q2None, Q2Send, Q2Recv} Q2;"                          +"\n"+
		            ""                                                                     +"\n"+
		            "void f2(){"                                                           +"\n"+
		            "     printf(\"C\");"                                                    +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void g2(){"                                                           +"\n"+
		            "     printf(\"D\");"                                                    +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "//Inconsistency between case labels"                                  +"\n"+
		            "void f_EMU_2(Q1 q){"                                                  +"\n"+
		            "     switch (q){"                                                     +"\n"+
		            "          case Q1Send: f2(); break;"                                  +"\n"+
		            "          case Q2Recv: g2(); break;"                                  +"\n"+
		            "     }"                                                               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "EMU"
		            ,
		            },
	/////////////////  2   ///////////////////	
		            {
		            "#include<stdio.h>"                                                    +"\n"+
		            "void f_EMU_3()"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            " enum ghx_emu_1_1 {x1, x2, x3, x4, x5};"                              +"\n"+
		            " enum ghx_emu_1_1 i, j, k, p;"                                        +"\n"+
		            " int n, m;"                                                           +"\n"+
		            " n = 0;"                                                              +"\n"+
		            "  for(j=x1; j<=x5; j++)"                                              +"\n"+
		            "   if(i!=x2)         //FP"                                        +"\n"+
		            "   {"                                                                 +"\n"+
		            "     if((k!=i)&&(k!=j))//FP"                                          +"\n"+
		            "     {"                                                               +"\n"+
		            "      n++;"                                                           +"\n"+
		            "      printf(\"%d\", n);"                                               +"\n"+
		            "      for(m=1; m<=3; m++)"                                            +"\n"+
		            "      {"                                                              +"\n"+
		            "       switch(m)"                                                     +"\n"+
		            "       {"                                                             +"\n"+
		            "       case 1: p = i;"                                                +"\n"+
		            "               break;"                                                +"\n"+
		            "       case 2: p = j;"                                                +"\n"+
		            "               break;"                                                +"\n"+
		            "       case 3: p = k;"                                                +"\n"+
		            "               break;"                                                +"\n"+
		            "       default:"                                                      +"\n"+
		            "               break;"                                                +"\n"+
		            "       }"                                                             +"\n"+
		            "       switch(p)"                                                     +"\n"+
		            "       {"                                                             +"\n"+
		            "       case x1:   printf(\"%s\", \"x1\");//FP"                        +"\n"+
		            "              break;"                                                 +"\n"+
		            "       case x2:    printf(\"%s\", \"x2\");//FP"                       +"\n"+
		            "              break;"                                                 +"\n"+
		            "       case x3: printf(\"%s\", \"x3\");//FP"                          +"\n"+
		            "              break;"                                                 +"\n"+
		            "       case x4: printf(\"%s\", \"x4\");//FP"                          +"\n"+
		            "              break;"                                                 +"\n"+
		            "       case x5:  printf(\"%s\", \"x5\");//FP"                         +"\n"+
		            "              break;"                                                 +"\n"+
		            "       default:"                                                      +"\n"+
		            "              break;"                                                 +"\n"+
		            "       }"                                                             +"\n"+
		            "      }"                                                              +"\n"+
		            "      printf(\"\\n\");"                                                  +"\n"+
		            "     }"                                                               +"\n"+
		            "   }"                                                                 +"\n"+
		            "   printf(\"%d\\n\", n);"                                                +"\n"+
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
