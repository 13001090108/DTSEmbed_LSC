package softtest.test.c.gcc.test_team_1;

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
public class NPD extends ModelTestBase {
	public NPD(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/NPD-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("fault");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
		
		//加载库函数摘要
		LIB_SUMMARYS_PATH="gcc_lib/npd_summary.xml";
		libManager.loadSingleLibFile(LIB_SUMMARYS_PATH);
		libManager.loadSingleLibFile("gcc_lib/lib_summary.xml");
		Set<MethodNameDeclaration> libDecls = libManager.compileLib(pre.getLibIncludes());
		interContext = InterContext.getInstance();
		interContext.addLibMethodDecl(libDecls);
	}
	 @Parameters
	 public static Collection<Object[]> testcaseAndResults()
	 {
		 return Arrays.asList(new Object[][] {

					/////////////////  0   ///////////////////
				 /////////////最后一个语句，from区间为unknow,结果应该为OK///////////////
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void ghx_npd_2_f2(int flag,char* to)"                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	char* from;"                                                         +"\n"+
		            "    char* buffer =(char*) calloc(1, 10);"                             +"\n"+
		            "	if(buffer){"                                                         +"\n"+
		            "	}"                                                                   +"\n"+
		            "    if (flag== 0) {"                                                  +"\n"+
		            "		from = to;"                                                         +"\n"+
		            "    }"                                                                +"\n"+
		            "    else {"                                                           +"\n"+
		            "        from = buffer;"                                               +"\n"+
		            "    }"                                                                +"\n"+
		            "    memcpy(from, to, 10);"                                            +"\n"+
		            "	*from;//DEFECT"                                                      +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  1   ///////////////////
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void ghx_npd_2_f2(int flag,char* to)"                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	char* from;"                                                         +"\n"+
		            "    char* buffer =(char*) calloc(1, 10);"                             +"\n"+
		            "	if(buffer){"                                                         +"\n"+
		            "	}"                                                                   +"\n"+
		            "    if (flag== 0) {"                                                  +"\n"+
		            "		from = to;"                                                         +"\n"+
		            "    }"                                                                +"\n"+
		            "    else {"                                                           +"\n"+
		            "        from = buffer;"                                               +"\n"+
		            "    }"                                                                +"\n"+
		            "    memcpy(from, to, 10);"                                            +"\n"+
		            "	*buffer;//DEFECT"                                                    +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },
		        	/////////////////  2   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "int ghx_npd_10_f10 ()"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "  int i;"                                                             +"\n"+
		            "  char * buffer;"                                                     +"\n"+
		            "  scanf (\"%d\", &i);"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "  buffer = (char*) malloc (i+1);"                                     +"\n"+
		            ""                                                                     +"\n"+
		            "  buffer[i]='\\0';//DEFECT"                                            +"\n"+
		            "  printf (\"%s\\n\",buffer);"                                            +"\n"+
		            "  free (buffer);"                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },
		        	/////////////////  3   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "int ghx_npd_10_f9 ()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "  int i;"                                                             +"\n"+
		            "  char * buffer;"                                                     +"\n"+
		            "  scanf (\"%d\", &i);"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "  buffer = (char*) malloc (i+1);"                                     +"\n"+
		            "  if (buffer==NULL) exit (1);"                                        +"\n"+
		            ""                                                                     +"\n"+
		            "else"                                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "  buffer[i]='\\0';//FP"                                                +"\n"+
		            ""                                                                     +"\n"+
		            "  printf (\"%s\\n\",buffer);"                                            +"\n"+
		            "  free (buffer);"                                                     +"\n"+
		            "}"                                                                    +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
////////////////	/  4   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void f(int flag){"                                                    +"\n"+
		            "    exit(0);"                                                         +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f1(int flag){"                                                   +"\n"+
		            "	int *i=malloc(1);"                                                   +"\n"+
		            "	if(!i)"                                                              +"\n"+
		            "    	f(flag);"                                                        +"\n"+
		            "	*i;"                                                                 +"\n"+
		            "	free(i);"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
////////////////	/  5  ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void f(int flag){"                                                    +"\n"+
		            "    if(flag) "                                                        +"\n"+
		            "       exit(0);"                                                      +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f1(int flag){"                                                   +"\n"+
		            "	int *i=malloc(1);"                                                   +"\n"+
		            "	if(!i)"                                                              +"\n"+
		            "    	f(flag);"                                                        +"\n"+
		            "	*i;"                                                                 +"\n"+
		            "	free(i);"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },
////////////////	/  6   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "struct st{"                                                    +"\n"+
		            "    int a; int b;"                                                         +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f1(int flag){"                                                   +"\n"+
		            "	struct st *i=malloc(sizeof(st));"                                                   +"\n"+
		            "	if(i->a)"                                                              +"\n"+
		            "    	;"                                                        +"\n"+
		            "	;"                                                                 +"\n"+
		            "	free(i);"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },
		            
		            
		            
		            
		 });
	 }
}
