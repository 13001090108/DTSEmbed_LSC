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
public class BO extends ModelTestBase{
	public BO(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/safety/BO-0.1.xml";
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
		 return Arrays.asList(new Object[][] 
				 {
	/////////////////  1   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "void f1()                                                           " +"\n"+
		            "{                                                                    "+"\n"+
		            "int a=6;                                                           "  +"\n"+
		            "char buffer2[10]=\"WELCOME\",buffer1[5],*p1=buffer1,*p2=buffer2;"       +"\n"+
		            "strncat(p1,buffer2,6);//DEFECT\"                                 "     +"\n"+
		            "strncat(p1,buffer2,5);//DEFECT\"                                 "     +"\n"+
		            "strncat(buffer1,p2,a);//DEFECT\"                                   "   +"\n"+
		            "}                                                                   " 
                    ,
                    "gcc"
                    ,
                    "BO"
                    ,
                    },
    /////////////////  2   ///////////////////	
                    {
                    "#include <string.h>"                                                  +"\n"+
                    "int f1(){                                                         "   +"\n"+
                    "int a=3,b;"                                                           +"\n"+
                    " if(a==3) b=10;"                                                      +"\n"+
                    " else b=9;"                                                           +"\n"+
                    "return b;"                                                            +"\n"+
                    "}                                                                   " +"\n"+
                    "void f2(){                                                          " +"\n"+
                    "int a;                                                         "      +"\n"+
                    "a=f1();                                                        "      +"\n"+
                    "char buffer[a];                                              "        +"\n"+
                    "strcpy(buffer,\"1234567890\");                                   "      +"\n"+
                    "}"                                                                    
                    ,
                    "gcc"
                    ,
                    "BO"
                    ,
                    },
    /////////////////  3   ///////////////////	
                    {
                    "#include  <stdio.h>"                                                  +"\n"+
                    "int all=8;"                                                           +"\n"+
                    "void f()"                                                             +"\n"+
                    "{                                                                "    +"\n"+
                    "all=6;"                                                               +"\n"+
                    "}                                                               "     +"\n"+
                    "void f1(){                                                           "+"\n"+
                    "f();                                                           "      +"\n"+
                    "char buffer[all];                                               "     +"\n"+
                    "scanf(\"%7s\",buffer);                                           "      +"\n"+
                    "}"                                                                    
                    ,
                    "gcc"
                    ,
                    "BO"
                    ,
                    },
    /////////////////  4   ///////////////////	
                    {
                    "#include<string.h>"                                                   +"\n"+
                    "#include<stdio.h>"                                                    +"\n"+
                    "int main(){ "                                                         +"\n"+
                    "    "                                                                 +"\n"+
                    "    char a[10];"                                                      +"\n"+
                    "    char b[100];"                                                     +"\n"+
                    "    strncpy(a,b,100);"                                                +"\n"+
                    "    }"                                                                
                    ,
                    "gcc"
                    ,
                    "BO"
                    ,
                    },
		 });
}
}

