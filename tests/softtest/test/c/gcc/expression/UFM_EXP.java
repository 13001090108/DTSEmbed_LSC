package softtest.test.c.gcc.expression;

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
	/////////////////  0   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            "typedef struct{"                                                      +"\n"+
		            "   char* p;"                                                          +"\n"+
		            "}S;"                                                                  +"\n"+
		            "S s;"                                                                 +"\n"+
		            ""                                                                     +"\n"+
		            "void f(){"                                                            +"\n"+
		            "   s.p=(char*)malloc(11);"                                            +"\n"+
		            "   free(s.p);"                                                        +"\n"+
		            "   *(s.p);"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM"
		            ,
		            },

	/////////////////  1   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            "typedef struct{"                                                      +"\n"+
		            "   char* p;"                                                          +"\n"+
		            "}S;"                                                                  +"\n"+
		            "S s;"                                                                 +"\n"+
		            "char* f(){"                                                           +"\n"+
		            "   return  (char*)malloc(11);"                                        +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f(){"                                                            +"\n"+
		            "   s.p=f();"                                                          +"\n"+
		            "   free(s.p);"                                                        +"\n"+
		            "   *(s.p);"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM"
		            ,
		            },

		 });
	 }
}
