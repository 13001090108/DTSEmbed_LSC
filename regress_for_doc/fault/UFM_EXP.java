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
public class UFM_EXP extends ModelTestBase {
	public UFM_EXP(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/UFM_EXP-0.1.xml";
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

	/////////////////  1   ///////////////////	
		            {
		            "typedef struct"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "	char* x;"                                                            +"\n"+
		            "	int y;"                                                              +"\n"+
		            "} aa;"                                                                +"\n"+
		            "char* func(int m)"                                                    +"\n"+
		            "{"                                                                    +"\n"+
		            "	aa a;"                                                               +"\n"+
		            "	a.x = (char*)malloc(8);"                                             +"\n"+
		            "	a.y = m/7;"                                                          +"\n"+
		            "	if(a.y>3)"                                                           +"\n"+
		            "		free(a.x);"                                                         +"\n"+
		            "	return a.x; //DEFECT, UFM_EXP, a.x"                                  +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM_EXP"
		            ,
		            },


		 });
	 }
}
