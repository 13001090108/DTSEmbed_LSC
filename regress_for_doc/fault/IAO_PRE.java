package fault;

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
public class IAO_PRE extends ModelTestBase{
	public IAO_PRE(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/IAO_PRE-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("fault");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
		
		//加载库函数摘要
		LIB_SUMMARYS_PATH="gcc_lib/lib_summary.xml";
		libManager.loadSingleLibFile(LIB_SUMMARYS_PATH);
		Set<MethodNameDeclaration> libDecls = libManager.compileLib(pre.getLibIncludes());
		interContext = InterContext.getInstance();
		interContext.addLibMethodDecl(libDecls);
	}

	 @Parameters
	 public static Collection<Object[]> testcaseAndResults()
	 {
		 return Arrays.asList(new Object[][] {
	/////////////////  1   ///////////////////	
		            {
		            "#define int 1"                                                        +"\n"+
		            "int func2(bool, int, int);"                                           +"\n"+
		            "int func3(int, int);"                                                 +"\n"+
		            "void func1(bool flag, int a, int b)"                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (a > 2 && a < 10) {"                                              +"\n"+
		            "		func2(flag, a, b);"                                                 +"\n"+
		            "	} else {"                                                            +"\n"+
		            "		func2(flag, a, b); //DEFECT"                                        +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    +"\n"+
		            "int func2(bool flag, int var1, int var2)"                             +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (flag) {"                                                         +"\n"+
		            "		return var2 % var1;"                                                +"\n"+
		            "	} else {"                                                            +"\n"+
		            "		return func3(var1, var2);"                                          +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    +"\n"+
		            "int func3(int var1, int var2)"                                        +"\n"+
		            "{"                                                                    +"\n"+
		            "	var2 /= var1;"                                                       +"\n"+
		            "	return var2;"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "IAO_PRE"
		            ,
		            },




		 });
	 }
}
