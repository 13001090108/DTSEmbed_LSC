package softtest.test.gcc.rules.question;

import java.util.Arrays;
import java.util.Collection;

import org.junit.BeforeClass;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import softtest.fsm.c.FSMLoader;
import softtest.fsm.c.FSMMachine;
import softtest.fsmanalysis.c.FSMAnalysisVisitor;
import softtest.test.c.rules.ModelTestBase;

@RunWith(Parameterized.class)
public class BSTR_FUNC_REALLOC extends ModelTestBase{
	public BSTR_FUNC_REALLOC(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/BSTR_FUNC_REALLOC-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("question");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
	}
	 @Parameters
	 public static Collection<Object[]> testcaseAndResults()
	 {
		 return Arrays.asList(new Object[][] {
	/////////////////  0   ///////////////////	
		            {
		            "#include<wtypes.h>"                                                   +"\n"+
		            "void bstr_realloc() {"                                                +"\n"+
		            "    BSTR foo = SysAllocString(L\"abc\"), bar; "                         +"\n"+
		            "  	wchar_t *baf = L\"abc\", *x = L\"xyz\";"                               +"\n"+
		            "  	foo = SysReAllocString(&baf, x); //defect "                        +"\n"+
		            "  	foo = SysReAllocString(&foo, bar); // defect"                      +"\n"+
		            "    foo = SysReAllocString(&foo, x);"                                 +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BSTR_FUNC_REALLOC"
		            ,
		            },
		 });
	 }
}
