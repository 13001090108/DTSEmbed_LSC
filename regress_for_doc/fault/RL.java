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
public class RL extends ModelTestBase{
	public RL(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/RL-0.1.xml";
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

	/////////////////  1   ///////////////////	
		            {
		            "#include <winsock2.h>"                                                +"\n"+
		            "int func2(SOCKET s)"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	SOCKET new_sock = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP); "       +"\n"+
		            "	//do_something(new_sock); "                                          +"\n"+
		            "	//closesocket(new_sock);  RL"                                        +"\n"+
		            "	return 0;//DEFECT, RL, new_sock"                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "RL"
		            ,
		            },
	/////////////////  2   ///////////////////	
		            {
		            "#include <winsock2.h>"                                                +"\n"+
		            "int func4 (int portnum)"                                              +"\n"+
		            "{"                                                                    +"\n"+
		            "	SOCKET s; "                                                          +"\n"+
		            "	s = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);"                      +"\n"+
		            "	if (s == INVALID_SOCKET) "                                           +"\n"+
		            "	return INVALID_SOCKET;"                                              +"\n"+
		            "	if (bind(s, (struct sockaddr *)&s, sizeof(struct sockaddr_in)) == SOCKET_ERROR) { "+"\n"+
		            "		closesocket(s); "                                                   +"\n"+
		            "		return(INVALID_SOCKET); "                                           +"\n"+
		            "	} "                                                                  +"\n"+
		            "	return 1;//DEFECT, RL, s"                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "RL"
		            ,
		            },
	/////////////////  3   ///////////////////	
		            {
		            "#include <winsock2.h>"                                                +"\n"+
		            "int func7 (int portnum)"                                              +"\n"+
		            "{"                                                                    +"\n"+
		            "	SOCKET s; "                                                          +"\n"+
		            "	s = socket(AF_INET, SOCK_STREAM, 0);"                                +"\n"+
		            "	if (s != INVALID_SOCKET) {"                                          +"\n"+
		            "		if (bind(s, (struct sockaddr *)&sa, sizeof(struct sockaddr_in)) == SOCKET_ERROR) { "+"\n"+
		            "		closesocket(s); "                                                   +"\n"+
		            "		return(INVALID_SOCKET); "                                           +"\n"+
		            "		} else {"                                                           +"\n"+
		            "		int a = 1;"                                                         +"\n"+
		            "		a = 1;"                                                             +"\n"+
		            "		} "                                                                 +"\n"+
		            "	}"                                                                   +"\n"+
		            "	return 1;//DEFECT, RL, s"                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "RL"
		            ,
		            },


		            

		 });
	 }
}
