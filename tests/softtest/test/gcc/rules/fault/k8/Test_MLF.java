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
public class Test_MLF extends ModelTestBase {
	public Test_MLF(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/MLF-0.1.xml";
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

				// 下面的用例对应模式MLF_FREE，但没有找到
				// 该模式，故先放在本文件中，待以后使用。
				// 2011年12月30日 zhhailon
//				//////////////////////////0//////////////////////////////////////////////
//				{
//					"void my_free(char *p, int flag) {"                                    +"\n"+
//							"		      if (flag == 17) {"                                            +"\n"+
//							"		          p = 0;"                                                   +"\n"+
//							"		          return;   //defect"                                       +"\n"+
//							"		      }"                                                            +"\n"+
//							"		      if (flag == 34) {"                                            +"\n"+
//							"		          return;   //defect"                                       +"\n"+
//							"		      }"                                                            +"\n"+
//							"		      free(p);"                                                     +"\n"+
//							"		 }"                                                            
//							,
//							"gcc"
//							,
//							"MLF"
//							,
//				},

		});
	}
}
