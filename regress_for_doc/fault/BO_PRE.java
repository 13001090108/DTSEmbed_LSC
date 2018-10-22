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
public class BO_PRE extends ModelTestBase{
	public BO_PRE(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/BO_PRE-0.1.xml";
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
		            "#include <stdio.h>       "                                            +"\n"+
		            "void f1(int a)                    "                                   +"\n"+
		            "{                                 "                                   +"\n"+
		            "	char buffer1[a];                 "                                   +"\n"+
		            "	scanf(\"%12s\",buffer1);//DEFECT   "                                   +"\n"+
		            "}                                 "                                   +"\n"+
		            "void f2()                         "                                   +"\n"+
		            "{                                 "                                   +"\n"+
		            "	int a=10;                        "                                   +"\n"+
		            "	f1(a);//DEFECT                   "                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO_PRE"
		            ,
		            },
		            
	/////////////////  2   ///////////////////	
		            {
		            "#include <string.h>          "                                        +"\n"+
		            "char g_array[10];            "                                        +"\n"+
		            "void func2(char*);           "                                        +"\n"+
		            "void func1()                 "                                        +"\n"+
		            "{                            "                                        +"\n"+
		            "	char *str = \"This is a too long string\";                        "    +"\n"+
		            "	func2(str); //DEFECT        "                                        +"\n"+
		            "}                                                         "           +"\n"+
		            "void func2(char *ptr)        "                                        +"\n"+
		            "{                            "                                        +"\n"+
		            "	strcpy(g_array, ptr);       "                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO_PRE"
		            ,
		            },

		            
	/////////////////  3   ///////////////////	
		            {
		            "void f1(char* p)                    "                                 +"\n"+
		            "{                                 "                                   +"\n"+
		            "	scanf(\"%12s\",p); "                                                   +"\n"+
		            "}                                 "                                   +"\n"+
		            "void f2()                         "                                   +"\n"+
		            "{                                 "                                   +"\n"+
		            "	typedef struct{"                                                     +"\n"+
		            "		char x[10];"                                                        +"\n"+
		            "	} aa;"                                                               +"\n"+
		            "	aa a;"                                                               +"\n"+
		            "	char* p=a.x;"                                                        +"\n"+
		            "	f1(p);//DEFECT"                                                      +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO_PRE"
		            ,
		            },

		            
 
	/////////////////  4   ///////////////////	
		            {
		            "typedef struct{"                                                      +"\n"+
		            "	char array[10];"                                                     +"\n"+
		            "} aa; "                                                               +"\n"+
		            "aa g;"                                                                +"\n"+
		            "void func2(char*);                                     "              +"\n"+
		            "void func1()                 "                                        +"\n"+
		            "{                        "                                            +"\n"+
		            "	char *str = \"This is a too long string\";                       "     +"\n"+
		            "	func2(str); //DEFECT        "                                        +"\n"+
		            "}                                                     "               +"\n"+
		            "void func2(char *ptr)        "                                        +"\n"+
		            "{                            "                                        +"\n"+
		            "	strcpy(g.array, ptr);"                                               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO_PRE"
		            ,
		            },
  

		 });
	 }
}
