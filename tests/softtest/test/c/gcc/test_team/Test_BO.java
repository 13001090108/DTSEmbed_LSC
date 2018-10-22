package softtest.test.c.gcc.test_team;


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
public class Test_BO extends ModelTestBase{
	public Test_BO(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/BO-0.1.xml";
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
	/////////////////  0   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "     char s[8];"                                                      +"\n"+
		            "     strcpy(s, \"0123456789\");//DEFECT"                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
	/////////////////  1   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "     char s[10] = \"abcdefg\";"                                         +"\n"+
		            "     char s1[5] = \"1234\";"                                            +"\n"+
		            "     strcat(s, s1);//DEFECT"                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
	/////////////////  2   ///////////////////	
//		            {
//		            "#include <stdlib.h>"                                                  +"\n"+
//		            "#include <string.h>"                                                  +"\n"+
//		            "void f(int i)"                                                        +"\n"+
//		            "{"                                                                    +"\n"+
//		            "    char *p;"                                                         +"\n"+
//		            "    if(i>10)"                                                         +"\n"+
//		            "        p = (char*)malloc(10*sizeof(char));"                          +"\n"+
//		            "    else"                                                             +"\n"+
//		            "        p = (char*)malloc(5*sizeof(char));"                           +"\n"+
//		            "    strcpy(p, \"abcdef\");//DEFECT//chh  i的值不确定，无法确定p的空间，无法判断是否BO"                                     +"\n"+
//		            "    free(p);"                                                         +"\n"+
//		            "}"                                                                    
//		            ,
//		            "gcc"
//		            ,
//		            "BO"
//		            ,
//		            },
//chh  针对上面的用例进行如下修改
		            {
			            "#include <stdlib.h>"                                                  +"\n"+
			            "#include <string.h>"                                                  +"\n"+
			            "void f()"                                                        +"\n"+
			            "{	 int i=9;"                                                                    +"\n"+
			            "    char *p;"                                                         +"\n"+
			            "    if(i>10)"                                                         +"\n"+
			            "        p = (char*)malloc(10*sizeof(char));"                          +"\n"+
			            "    else"                                                             +"\n"+
			            "        p = (char*)malloc(5*sizeof(char));"                           +"\n"+
			            "    strcpy(p, \"abcdef\");//DEFECT//chh  i的值不确定，无法确定p的空间，无法判断是否BO"                                     +"\n"+
			            "    free(p);"                                                         +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "BO"
			            ,
			            },	            


		
			 
		 });
	 }
}

