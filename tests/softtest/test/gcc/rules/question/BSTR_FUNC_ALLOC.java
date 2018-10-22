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
public class BSTR_FUNC_ALLOC extends ModelTestBase {
	public BSTR_FUNC_ALLOC(String source, String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/BSTR_FUNC_ALLOC-0.1.xml";
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
            "void bstr_alloc() {"                                                  +"\n"+
            "	 BSTR foo = SysAllocString(L\"abc\"), bar;"                            +"\n"+
            "	 bar = SysAllocString(foo);  // defect"                              +"\n"+
            "}"                                                                    
            ,
            "gcc"
            ,
            "BSTR_FUNC_ALLOC"
            ,
            },
/////////////////  1   ///////////////////	
        {
        "#include<wtypes.h>"                                                   +"\n"+
        "void bstr_alloc() {"                                                  +"\n"+
        "	 BSTR foo = SysAllocStringLen(L\"abc\");	  			"                        +"\n"+
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
