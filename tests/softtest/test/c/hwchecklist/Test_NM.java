package softtest.test.c.hwchecklist;

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
public class Test_NM extends ModelTestBase{
    public Test_NM(String source, String compiletype, String result) {
    	super(source, compiletype, result);
    }

    @BeforeClass
    public static void setUpBaseChild() {
    	fsmPath = "softtest/rules/gcc/rule/HW_6_1_NM-0.1.xml";
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
    public static Collection<Object[]> testcaseAndResults() {
        return Arrays.asList(new Object[][] {
/////////////////  0   zys 2011.6.24	需要添加malloc的函数原型///////////////////	
                {
                "#include <stdlib.h>"                                                             +"\n"+
                "void f()"                                                             +"\n"+
                "{"                                                                    +"\n"+
                " 	int* p=(int*)malloc(1);"                                            +"\n"+
                "}"                                                                    
                ,
                "gcc"
                ,
                "HW_6_1_NM"
                ,
                },
/////////////////  1   ///////////////////	
                {
                "void f()"                                                             +"\n"+
                "{"                                                                    +"\n"+
                " 	int a;"                                                             +"\n"+
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
