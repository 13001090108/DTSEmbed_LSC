package softtest.test.gcc.rules.fault.k8;

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
public class Test_UVF_P extends ModelTestBase{
	public Test_UVF_P(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/UVF_P-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("fault");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);

		//加载库函数摘要
		LIB_SUMMARYS_PATH="gcc_lib/bo_summary.xml";
		libManager.loadSingleLibFile(LIB_SUMMARYS_PATH);
		Set<MethodNameDeclaration> libDecls = libManager.compileLib(pre.getLibIncludes());
		interContext = InterContext.getInstance();
		interContext.addLibMethodDecl(libDecls);
	}

	@Parameters
	public static Collection<Object[]> testcaseAndResults()
	{
		return Arrays.asList(new Object[][] {

				//////////////////////////0/////////////////////////////////////////////
				{//复杂结构变量的指针变量，待解决
					"struct s {"                                                           +"\n"+
							"    int i;"                                                           +"\n"+
							"  };"                                                                 +"\n"+
							"  int f(struct s **v, int t) {"                                       +"\n"+
							"    *v = (struct s *)malloc(sizeof(struct s));"                       +"\n"+
							"    if (t > 0) {"                                                     +"\n"+
							"      (*v)->i = t;"                                                   +"\n"+
							"    }"                                                                +"\n"+
							"   return (*v)->i; //defect"                                          +"\n"+
							"}"  
							,
							"gcc"
							,
							"UVF_P"
							,
				},
				///////////////////////////////1/////////////////////////////////
				{//复杂结构变量的指针变量，待解决
					"#include<stdlib.h>"                                                   +"\n"+
							"typedef struct {"                                                     +"\n"+
							"    int x;"                                                           +"\n"+
							"    int y;"                                                           +"\n"+
							"} S1;"                                                                +"\n"+
							"typedef struct {"                                                     +"\n"+
							"    S1* ptr;"                                                         +"\n"+
							"   int z;"                                                            +"\n"+
							"} S2;"                                                                +"\n"+
							"void fun1(S1* local_ptr) {"                                           +"\n"+
							"   int k = local_ptr->x;"                                             +"\n"+
							"}"                                                                    +"\n"+
							"intmain() {"                                                          +"\n"+
							"   S2* main_ptr = (S2*)malloc(100);"                                  +"\n"+
							"   if(main_ptr != NULL) {"                                            +"\n"+
							"     	fun1(main_ptr->ptr); //defect"                                  +"\n"+
							"     	free(main_ptr);"                                                +"\n"+
							"  }"                                                                  +"\n"+
							"   return 0;"                                                         +"\n"+
							"}"
							,
							"gcc"
							,
							"UVF_P"
							,
				},	
		});
	}
}
