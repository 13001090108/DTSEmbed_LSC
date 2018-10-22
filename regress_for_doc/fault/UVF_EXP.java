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
public class UVF_EXP extends ModelTestBase{
	public UVF_EXP(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/UVF_Exp-0.1.xml";
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
	/////////////////  1   ///////////////////	
		            {
		            "struct x"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "	int y;"                                                              +"\n"+
		            "	char a;"                                                             +"\n"+
		            "};"                                                                   +"\n"+
		            "void fun()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "	struct x xx;"                                                        +"\n"+
		            "	int k;"                                                              +"\n"+
		            "	xx.y=1;"                                                             +"\n"+
		            "	k=xx.y;"                                                             +"\n"+
		            "	char b=xx.a; //DEFECT, UVF_EXP, xx.a"                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UVF_EXP"
		            ,
		            },


		 });
	 }
}
