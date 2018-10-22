package softtest.test.android.gcc;

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
public class RL_PRE extends ModelTestBase {
	public RL_PRE(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/RL_PRE-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("fault");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);

		//加载库函数摘要
		LIB_SUMMARYS_PATH="gcc_lib/rm_summary.xml";
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
	            "#include<stdio.h>"                                                    +"\n"+
	            "void read_global_stats(int erase) {"                                  +"\n"+
	            "    FILE *f;"                                                         +"\n"+
	            "    if (erase) {"                                                     +"\n"+
	            "        f = fopen(0, \"w\");"                                         +"\n"+
	            "        if (!f) {"                                                    +"\n"+
	            "            fprintf(0, \"Could not open global latency stats file: %s\\n\", 0);"+"\n"+
	            "            exit(1);"                                                 +"\n"+
	            "        }"                                                            +"\n"+
	            "        fprintf(f, \"erase\\n\");"                                    +"\n"+
	            "        fclose(f);"                                                   +"\n"+
	            "    }"                                                                +"\n"+
	            ""                                                                     +"\n"+
	            "    f = fopen(0, \"r\");"                                             +"\n"+
	            "    if (!f) {"                                                        +"\n"+
	            "        fprintf(0, \"Could not open global latency stats file: %s\\n\", 0);"+"\n"+
	            "        exit(1);"                                                     +"\n"+
	            "    }"                                                                +"\n"+
	            ""                                                                     +"\n"+
	            "    fclose(f);"                                                       +"\n"+
	            ""                                                                     +"\n"+
	            "    return;"                                                          +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "OK"           
	            },

		
		});
	}
}