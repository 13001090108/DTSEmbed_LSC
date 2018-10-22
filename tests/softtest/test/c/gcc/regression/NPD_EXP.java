package softtest.test.c.gcc.regression;

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
public class NPD_EXP extends ModelTestBase {
	public NPD_EXP(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/NPD_EXP-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("fault");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
		
		//加载库函数摘要
		LIB_SUMMARYS_PATH="gcc_lib/npd_summary.xml";
		libManager.loadSingleLibFile(LIB_SUMMARYS_PATH);
		Set<MethodNameDeclaration> libDecls = libManager.compileLib(pre.getLibIncludes());
		interContext = InterContext.getInstance();
		interContext.addLibMethodDecl(libDecls);
	}
	
	 @Parameters
	 public static Collection<Object[]> testcaseAndResults()
	 {
		 return Arrays.asList(new Object[][] {
	/////////////////  0   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <malloc.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "void npd_f1(){"                                                       +"\n"+
		            "    struct pb{"                                                       +"\n"+
		            "	   char *c;"                                                         +"\n"+
		            "	};"                                                                  +"\n"+
		            "	struct pc{"                                                          +"\n"+
		            "	   struct pb* B;"                                                    +"\n"+
		            "	}C;"                                                                 +"\n"+
		            "	C.B->c= NULL;"                                                       +"\n"+
		            "	*(C.B->c) = 'c'; //Defect,NPD_EXP,C.B->c"                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            ,
		            },
	/////////////////  1   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <malloc.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "void npd_f2(){"                                                       +"\n"+
		            "    struct pb{"                                                       +"\n"+
		            "	   char *c;"                                                         +"\n"+
		            "	};"                                                                  +"\n"+
		            "	struct pc{"                                                          +"\n"+
		            "	   struct pb* B;"                                                    +"\n"+
		            "	}C;"                                                                 +"\n"+
		            "	char ch;"                                                            +"\n"+
		            "	C.B->c= &ch;"                                                        +"\n"+
		            "	*(C.B->c) = 'c'; //FP"                                               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  2   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <malloc.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "void npd_f3(){"                                                       +"\n"+
		            "	struct p{"                                                           +"\n"+
		            "	   int *i;"                                                          +"\n"+
		            "	}A;"                                                                 +"\n"+
		            "	A.i = (int *)malloc(4);"                                             +"\n"+
		            "	*(A.i) = 1; //Defect,NPD_EXP,A.i"                                    +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            ,
		            },
	/////////////////  3   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <malloc.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "int npd_f4(){"                                                        +"\n"+
		            "	struct p{"                                                           +"\n"+
		            "	   int *i;"                                                          +"\n"+
		            "	}A;"                                                                 +"\n"+
		            "	A.i = (int *)malloc(4);"                                             +"\n"+
		            "	if(A.i == NULL)"                                                     +"\n"+
		            "	   return 0;"                                                        +"\n"+
		            "	else"                                                                +"\n"+
		            "	   *(A.i) = 1;//FP"                                                  +"\n"+
		            "	return 1;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  4   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <malloc.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "int npd_f5(){"                                                        +"\n"+
		            "	struct p{"                                                           +"\n"+
		            "	   int *x;"                                                          +"\n"+
		            "       int **y;"                                                      +"\n"+
		            "	}A;"                                                                 +"\n"+
		            "	A.x = NULL;"                                                         +"\n"+
		            "    A.y = NULL;"                                                      +"\n"+
		            "    **(A.y) = 2;//Defect,NPD_EXP,A.y"                                             +"\n"+
		            "	return 1;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            ,
		            },
	/////////////////  5   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <malloc.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "void npd_f7(){"                                                       +"\n"+
		            "	struct p{"                                                           +"\n"+
		            "	   int *i;"                                                          +"\n"+
		            "	}A;"                                                                 +"\n"+
		            "	A.i = (int *)malloc(4);"                                             +"\n"+
		            "	if(A.i != NULL && *(A.i) == 1)//FP,OK"                               +"\n"+
		            "	   *(A.i) = 2; //FP,OK"                                              +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  6   ///////////////////	
		            {
		            "#include  <stdio.h>"                                                  +"\n"+
		            "typedef  struct{"                                                     +"\n"+
		            "    char a[22];"                                                      +"\n"+
		            "    char* p;"                                                         +"\n"+
		            "}S;"                                                                  +"\n"+
		            "S  *s1,*s2;"                                                          +"\n"+
		            "void f(){"                                                            +"\n"+
		            "   s1->p=(char*)malloc(11);"                                          +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f1(){"                                                           +"\n"+
		            "   f();"                                                              +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2(){"                                                           +"\n"+
		            "   f1();"                                                             +"\n"+
		            "   *(s1->p)='a';"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            ,
		            },
	/////////////////  7   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "typedef struct{"                                                      +"\n"+
		            "  char* p;"                                                           +"\n"+
		            "}S;"                                                                  +"\n"+
		            "S *s;"                                                                +"\n"+
		            "void f(){"                                                            +"\n"+
		            "   s->p=0;"                                                           +"\n"+
		            "   *(s->p);"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            ,
		            },
/////////////////  8   ///////////////////
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_exp_2_f1()"                                               +"\n"+
		            "{"                                                                    +"\n"+
		            "	int *ptr;"                                                           +"\n"+
		            ""                                                                     +"\n"+
		            "	ptr = (int*)malloc(4 * sizeof(int));"                                +"\n"+
		            "	if (!ptr)"                                                           +"\n"+
		            "		return;"                                                            +"\n"+
		            "	*(ptr + 2) = 5; //FP"                                                +"\n"+
		            "	free(ptr);"                                                          +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
/////////////////  9   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                  +"\n"+
		            "char *ghx_npd_4_f4(char *b)"                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "    int i, m, n;"                                                     +"\n"+
		            "    char *s;"                                                         +"\n"+
		            ""                                                                     +"\n"+
		            "    m = strlen(b);"                                                   +"\n"+
		            "    n = m;"                                                           +"\n"+
		            "    s = (char *) malloc(n + 1);"                                      +"\n"+
		            "    for (i = 0; i < m; i++)"                                          +"\n"+
		            "	{"                                                                   +"\n"+
		            "        *(s + i) = *(b + i);//DEFECT"                                 +"\n"+
		            "	}"                                                                   +"\n"+
		            "    *(s + m) = NULL;"                                                 +"\n"+
		            "    return (s);"                                                      +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            ,
		            },
/////////////////  10   ///////////////////
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "#include <string.h>"                                                  +"\n"+
		            "struct ghx_npd_5_s5"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	char* ss;"                                                           +"\n"+
		            ""                                                                     +"\n"+
		            "};"                                                                   +"\n"+
		            "void ghx_npd_5_f5()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	struct ghx_npd_5_s5 s;"                                              +"\n"+
		            "	s.ss=(char*)malloc(10);"                                             +"\n"+
		            "	char* a=(char*)malloc(10);"                                          +"\n"+
		            "	s.ss[0]=*a;//DEFECT"                                                 +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            ,
		            },

		 });
	 }
}
