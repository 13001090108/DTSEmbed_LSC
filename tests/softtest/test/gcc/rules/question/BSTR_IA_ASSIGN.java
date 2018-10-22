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
public class BSTR_IA_ASSIGN extends ModelTestBase{
	public BSTR_IA_ASSIGN(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/question/BSTR_IA_ASSIGN-0.1.xml";
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
		            "	#include<wtypes.h>"                                                  +"\n"+
		            "	void bstr_assign() {"                                                +"\n"+
		            "	  			BSTR foo;"                                                      +"\n"+
		            "	  			wchar_t *bar = L\"abc\";"                                         +"\n"+
		            "	  			foo = bar; // defect"                                           +"\n"+
		            "	}"                                                                   
		            ,
		            "gcc"
		            ,
		            "BSTR_IA_ASSIGN"
		            ,
		            },	
    /////////////////  1   ///////////////////	
		            {
		            "	#include<wtypes.h>"                                                  +"\n"+
		            "	void bstr_assign() {"                                                +"\n"+
		            "	  			BSTR foo;"                                                      +"\n"+
		            "	  			foo = NULL;  "                                           +"\n"+
		            "	}"                                                                   
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },	
		 });
	 }
}
