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
public class UFM_PRE extends ModelTestBase {
	public UFM_PRE(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/UFM_PRE-0.1.xml";
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
		          //hcj函数摘要问题，待改进
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "int *g_ptr = NULL;"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int);"                                                     +"\n"+
		            "void func3();"                                                        +"\n"+
		            ""                                                                     +"\n"+
		            "void func1(int flag)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	g_ptr = (int*)malloc(sizeof(int));"                                  +"\n"+
		            "	func2(flag);"                                                        +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int flag)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (flag > 0) {"                                                     +"\n"+
		            "		free(g_ptr);"                                                       +"\n"+
		            "		func3(); //DEFECT"                                                  +"\n"+
		            "	}     "                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func3()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	(*g_ptr)++;"                                                         +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM_PRE"
		            ,
		            },
		        	/////////////////  1   ///////////////////	
			          //hcj函数摘要问题，待改进
			            {
			            "#include <stdlib.h>"                                                  +"\n"+
			            ""                                                                     +"\n"+
			            "int *g_ptr = NULL;"                                                   +"\n"+
			            ""                                                                     +"\n"+
			            "void func2(int);"                                                     +"\n"+
			            "void func3();"                                                        +"\n"+
			            ""                                                                     +"\n"+
			            "void func1(int flag)"                                                 +"\n"+
			            "{"                                                                    +"\n"+
			            "	g_ptr = (int*)malloc(sizeof(int));"                                  +"\n"+
			            "	func2(flag);"                                                        +"\n"+
			            "}"                                                                    +"\n"+
			            ""                                                                     +"\n"+
			            "void func2(int flag)"                                                 +"\n"+
			            "{"                                                                    +"\n"+
			            "	if (flag < 0) {"                                                     +"\n"+
			            "		func3(); //FP"                                                      +"\n"+
			            "		return;"                                                            +"\n"+
			            "	}"                                                                   +"\n"+
			            "}"                                                                    +"\n"+
			            ""                                                                     +"\n"+
			            "void func3()"                                                         +"\n"+
			            "{"                                                                    +"\n"+
			            "	(*g_ptr)++;"                                                         +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "OK"
			            ,
			            },
	/////////////////  2   ///////////////////	
		          //hcj函数摘要问题，待改进
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "#define SIZE 5"                                                       +"\n"+
		            ""                                                                     +"\n"+
		            "int *g_ptr = NULL;"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int);"                                                     +"\n"+
		            "void func3();"                                                        +"\n"+
		            ""                                                                     +"\n"+
		            "void func1(int flag)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	g_ptr = (int*)malloc(SIZE*sizeof(int));"                             +"\n"+
		            "	func2(flag);"                                                        +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int flag)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (flag > 0) {"                                                     +"\n"+
		            "		free(g_ptr);"                                                       +"\n"+
		            "		func3(); //DEFECT"                                                  +"\n"+
		            "	}"                                                                 +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func3()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	g_ptr[SIZE-1]++;"                                                    +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM_PRE"
		            ,
		            },
		        	/////////////////  3   ///////////////////	
			          //hcj函数摘要问题，待改进
			            {
			            "#include <stdlib.h>"                                                  +"\n"+
			            ""                                                                     +"\n"+
			            "#define SIZE 5"                                                       +"\n"+
			            ""                                                                     +"\n"+
			            "int *g_ptr = NULL;"                                                   +"\n"+
			            ""                                                                     +"\n"+
			            "void func2(int);"                                                     +"\n"+
			            "void func3();"                                                        +"\n"+
			            ""                                                                     +"\n"+
			            "void func1(int flag)"                                                 +"\n"+
			            "{"                                                                    +"\n"+
			            "	g_ptr = (int*)malloc(SIZE*sizeof(int));"                             +"\n"+
			            "	func2(flag);"                                                        +"\n"+
			            "}"                                                                    +"\n"+
			            ""                                                                     +"\n"+
			            "void func2(int flag)"                                                 +"\n"+
			            "{"                                                                    +"\n"+
			            "	if (flag < 0) {"                                                     +"\n"+
			            "		func3(); //FP"                                                      +"\n"+
			            "		return;"                                                            +"\n"+
			            "	}"                                                                   +"\n"+
			            "}"                                                                    +"\n"+
			            ""                                                                     +"\n"+
			            "void func3()"                                                         +"\n"+
			            "{"                                                                    +"\n"+
			            "	g_ptr[SIZE-1]++;"                                                    +"\n"+
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
