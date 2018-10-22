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
public class MLF_WRONG extends ModelTestBase {
	public MLF_WRONG(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/MLF_WRONG-0.1.xml";
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
				{
//////////////////////////0//////////////////////////////////////////////
					"#include \"stdlib.h\""                                          +"\n"+
					"char * p;"                                                      +"\n"+
					"void *ghx_mlf_1_f1()"                                           +"\n"+
					"{"                                                              +"\n"+
					"	char *ff =p;"                                                   +"\n"+
					"	free (ff);"                                                  +"\n"+
					"	return 0;"                                                   +"\n"+
					"}"                                                                    
					,
					"gcc"
		            ,
					"OK"
					,
				},	
/////////////////  1   ///////////////////	
				{
					"#include\"stdlib.h\" "                                                    +"\n"+
					"int *ptr;"                                                            +"\n"+
					"void func1()"                                                         +"\n"+
					"{"                                                                    +"\n"+
					"   int *ptr2;"                                                        +"\n"+
					"   ptr = (int *)malloc(10);"                                          +"\n"+
					"   free(ptr2);"                                                       +"\n"+
					"}"                                                                    
					,
					"gcc"
		            ,
					"MLF_WRONG"
					,
				},
/////////////////  2   ///////////////////	
	            {
	            "#include\"stdlib.h\" "                                                +"\n"+
	            "int *ptr;"                                                            +"\n"+
	            "void func1()"                                                         +"\n"+
	            "{"                                                                    +"\n"+
	            "   int *ptr2;"                                                        +"\n"+
	            "   ptr2 = (int *)malloc(5);"                                          +"\n"+
	            "   free(ptr2);"                                                       +"\n"+
	            "  // free(ptr);"                                                        +"\n"+
	            "}"                                                                    
	            ,
				"gcc"
	            ,
	            "OK"
				,
	            },
/////////////////  3   ///////////////////	
	            {
	            "#include\"stdlib.h\" "                                                 +"\n"+          
	            "void func1()"                                                         +"\n"+
	            "{"                                                                    +"\n"+
	            "   int *ptr;"                                                         +"\n"+
	            "   int *ptr2;"                                                        +"\n"+
	            "   ptr2 = (int *)malloc(5);"                                          +"\n"+
	            "   free(ptr2);"                                                       +"\n"+
	            "   free(ptr);"                                                        +"\n"+
	            "}"                                                                    
	            ,
				"gcc"
	            ,
	            "MLF_WRONG"
				,
	            },
/////////////////  4   ///////////////////	
	            {
	            "#include\"stdlib.h\" "                                                  +"\n"+
	            
	            "void func1()"                                                         +"\n"+
	            "{"                                                                    +"\n"+
	            "   int *ptr;"                                                         +"\n"+
	            "   int *ptr2;"                                                        +"\n"+
	            "   ptr2 = (int *)malloc(5);"                                               +"\n"+
	            "   free(ptr2);"                                                    +"\n"+
	            "}"                                                                    
	            ,
				"gcc"
	            ,
	            "OK"
				,
	            },
/////////////////  5   ///////////////////	
	            {
	            "#include\"stdlib.h\" "                                                  +"\n"+
	            "int *ptr;"                                                            +"\n"+
	            "void func1()"                                                         +"\n"+
	            "{"                                                                    +"\n"+
	            "   int *ptr2;"                                                        +"\n"+
	            "   ptr2 = func2();"                                                   +"\n"+
	            "   free(ptr2);"                                                    +"\n"+
	            "   free(ptr);"                                                     +"\n"+
	            "}"                                                                    +"\n"+
	            "int * func2()"                                                        +"\n"+
	            "{"                                                                    +"\n"+
	            "   return malloc(10);"                                                +"\n"+
	            "}"                                                                    
	            ,
				"gcc"
	            ,
	            "OK"
				,
	            },
/////////////////  6   ///////////////////	
	            {
	            "#include\"stdlib.h\" "                                                  +"\n"+
	            "int *ptr;"                                                            +"\n"+
	            "void func1()"                                                         +"\n"+
	            "{"                                                                    +"\n"+
	            "   int *ptr2;"                                                        +"\n"+
	            "   ptr2 = func2();"                                                   +"\n"+
	            "   free(ptr2);"                                                    +"\n"+
	            "   free(ptr);"                                                     +"\n"+
	            "}"                                                                    +"\n"+
	            "int * func2()"                                                        +"\n"+
	            "{"                                                                    +"\n"+
	            "   return (int *)malloc(10);"                                         +"\n"+
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