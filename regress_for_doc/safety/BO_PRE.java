package safety;


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
public class BO_PRE extends ModelTestBase{
	public BO_PRE(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/safety/BO_PRE-0.1.xml";
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
		            "#include <stdio.h>"                                                   +"\n"+
		            "void f1(char *p) "                                                    +"\n"+
		            "{                                                                	"   +"\n"+
		            "scanf(\"%12s\",p);   "                                                  +"\n"+
		            "}                                                           "         +"\n"+
		            "void f2()                                                            "+"\n"+
		            "{                                                                  "  +"\n"+
		            "char buffer[10],*p=buffer;                                         "  +"\n"+
		            "f1(p);//DEFECT\"                                                   "   +"\n"+
		            "}  "                                                                  
	                ,
	                "gcc"
	                ,
	                "BO_PRE"
	                ,
	                },
	/////////////////  2   ///////////////////	
	                {
	                "#include <string.h>"                                                  +"\n"+
	                "void f1(int a) "                                                      +"\n"+
	                "{"                                                                    +"\n"+
	                "char buffer2[15]=\"1234567890\",buffer1[10];"                           +"\n"+
	                "strncat (buffer1,buffer2,a);//DEFECT\"                                +\"\\n\"+"+"\n"+
	                "}                                                                  "  +"\n"+
	                "void f2()                                                            "+"\n"+
	                "{                                                                    "+"\n"+
	                "int a=11;                                                          "  +"\n"+
	                "f1(a);                                                              " +"\n"+
	                "}"                                                                    
	                ,
	                "gcc"
	                ,
	                "BO_PRE"
	                ,
	                },
	/////////////////  3   ///////////////////	
	                {
	                "#include <string.h>                                               "   +"\n"+
	                "                                                                   "  +"\n"+
	                "void f1(char *p) "                                                    +"\n"+
	                "{"                                                                    +"\n"+
	                "char buffer1[10];"                                                    +"\n"+
	                "strcpy (buffer1,p);"                                                  +"\n"+
	                "}                                                                  "  +"\n"+
	                "void f2()                                                            "+"\n"+
	                "{                                                                    "+"\n"+
	                "char buffer[15],*p=buffer;                                          " +"\n"+
	                "strcpy (p,\"1234567890\");                                           "  +"\n"+
	                "f1(p);//DEFECT\"                                                      "+"\n"+
	                "} "                                                                   
	                ,
	                "gcc"
	                ,
	                "BO_PRE"
	                ,
	                },
		 });
	 }
}
