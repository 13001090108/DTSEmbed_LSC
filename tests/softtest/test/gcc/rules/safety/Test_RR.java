package softtest.test.gcc.rules.safety;

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
public class Test_RR extends ModelTestBase{
	public Test_RR(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/safety/RR-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("safety");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
	}
	
	 @Parameters
	 public static Collection<Object[]> testcaseAndResults()
	 {
		 return Arrays.asList(new Object[][] {
////////////////////////0//////////////////////////////////////////////
			            {
			            "#include <stdio.h>"                                                   +"\n"+
			            "#include <windows.h>"                                                 +"\n"+
			            ""                                                                     +"\n"+
			            ""                                                                     +"\n"+
			            "LONG foo(HKEY hkey, LPCTSTR lpSubKey, DWORD ulOptions, PHKEY phkResult) "+"\n"+
			            "{"                                                                    +"\n"+
			            "	return RegOpenKeyEx(hkey, lpSubKey, ulOptions, KEY_ALL_ACCESS, phkResult);//DEFECT,RR"+"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "RR"
			            ,
			            },
//////////////////////1//////////////////////////////////////////////	
			            {
			            "#include<windows.h>"                                                  +"\n"+
			            "LONG func(LPTSTR lpMachineName,PHKEY phkResult){"                     +"\n"+
			            "	return RegConnectRegistry(lpMachineName,HKEY_LOCAL_MACHINE,phkResult);"+"\n"+
			            "}"                                                                    +"\n"+
			            "int main(){"                                                          +"\n"+
			            "	return 0;"                                                           +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "RR"
			            ,
			            },
//////////////////////////2//////////////////////////////////////////////	
			            {
			                "#include <windows.h>  "                                               +"\n"+
			                "int main() {  "                                                       +"\n"+
			                "   	SECURITY_DESCRIPTOR newSD; "                                      +"\n"+
			                "    if (!SetSecurityDescriptorDacl(&newSD, TRUE, NULL, FALSE)) {  "   +"\n"+
			                "    	return 0;"                                                       +"\n"+
			                "    }  "                                                              +"\n"+
			                "    return 0;"                                                        +"\n"+
			                "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "RR"
				            ,
				            },
		 });
	 }
}
