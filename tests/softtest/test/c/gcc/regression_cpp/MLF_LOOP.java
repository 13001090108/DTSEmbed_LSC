package softtest.test.c.gcc.regression_cpp;

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
public class MLF_LOOP extends ModelTestBase {
	public MLF_LOOP(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/MLF_LOOP-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("fault");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);

		//加载库函数摘要
		LIB_SUMMARYS_PATH="gcc_lib/npd_summary.xml";
		libManager.loadSingleLibFile(LIB_SUMMARYS_PATH);
		libManager.loadSingleLibFile("gcc_lib/npd_summary.xml");
		Set<MethodNameDeclaration> libDecls = libManager.compileLib(pre.getLibIncludes());
		interContext = InterContext.getInstance();
		interContext.addLibMethodDecl(libDecls);
	}

	@Parameters
	public static Collection<Object[]> testcaseAndResults()
	{
		return Arrays.asList(new Object[][] {

				//////////////////////////0//////////////////////////////////////////////
				{
					"#include \"stdlib.h\""                                                  +"\n"+
							"void *ghx_mlf_1_f1()"                                                 +"\n"+
							"{"                                                                    +"\n"+
							"	int cc;"                                                             +"\n"+
							"	char *ff;"                                                           +"\n"+
							""                                                                     +"\n"+
							"	for (cc=0; cc<500; cc++)"                                            +"\n"+
							"	{"                                                                   +"\n"+
							"		ff=(char*)malloc(10);"                                              +"\n"+
							"	}"                                                                   +"\n"+
							""                                                                     +"\n"+
							"	free (ff);"                                                  +"\n"+
							"	return 0;"                                                           +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"MLF_LOOP"
							,
				},
				//////////////////////////1//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"#define MAX 10"                                                       +"\n"+
							"void fun(){"                                                          +"\n"+
							"	char* ch;int i;"                                                           +"\n"+
							"	for(i=1;i<MAX;i++){"                                             +"\n"+
							"		ch=(char*)malloc(MAX);"                                             +"\n"+
							"	}"                                                                   +"\n"+
							"	free(ch);      "                                           +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"MLF_LOOP"
							,
				},
/////////////////  0   ///////////////////	
	            {
	            "#include <stdlib.h>"                                                  +"\n"+
	            "int foo_4_1() {"                                                      +"\n"+
	            "    char *p[10];"                                                     +"\n"+
	            "    int i=0;"                                                         +"\n"+
	            "    for(i=0;i<=9;i++){"                                               +"\n"+
	            "        p[i]= (char*)malloc(sizeof(char));"                           +"\n"+
	            "    }"                                                                +"\n"+
	            "    return 0;"                                                        +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "MLF_LOOP"
	            ,
	            },

		});
	}
}
