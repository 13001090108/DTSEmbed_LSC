package softtest.test.c.gcc.regression;

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
public class MLF_FREE extends ModelTestBase {
	public MLF_FREE(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/MLF_FREE-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("fault");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
		
		//加载库函数摘要
		LIB_SUMMARYS_PATH="gcc_lib/npd_summary.xml";
		libManager.loadSingleLibFile(LIB_SUMMARYS_PATH);
		libManager.loadSingleLibFile("gcc_lib/npd_summary.xml");
		Set<MethodNameDeclaration> libDecls = libManager.compileLib(pre.getLibIncludes());
		interContext = InterContext.getInstance();
		interContext.addLibMethodDecl(libDecls);
	}
	
	@Parameters
	public static Collection<Object[]> testcaseAndResults()
	{
		return Arrays.asList(new Object[][] {
//////////////////////////0//////////////////////////////////////////////
				 {
					 "#include <stdlib.h>"                                                  +"\n"+
					 "  void my_free(char *p, int flag) {"                                  +"\n"+
					 "      if (flag == 17) {"                                              +"\n"+
					 "          p = 0;"                                                     +"\n"+
					 "          return;  //DEFECT"                                          +"\n"+
					 "      }"                                                              +"\n"+
					 "      if (flag == 34) {"                                              +"\n"+
					 "          return; //DEFECT"                                           +"\n"+
					 "      }"                                                              +"\n"+
					 "      free(p);"                                                       +"\n"+
					 " }"																  +"\n"+
					 "  void foo()"                                                      +"\n"+
					 "  {"                                                                  +"\n"+
					 "      int *ptr;"                                                      +"\n"+
					 "      ptr = (int*)malloc(sizeof(int));"                               +"\n"+
					 "      my_free(ptr,1); //DEFECT"                                            +"\n"+
					 " }"                                                                   
					 ,
					 "gcc"
			         ,
					 "MLF_FREE"
					 ,
				 }, 
//////////////////////////1//////////////////////////////////////////////					 
				 {
				    "#include <stdlib.h>"                                                  +"\n"+
		            "  void my_free(char *p, int flag) {"                                  +"\n"+
		            "      if (flag == 17) {"                                              +"\n"+
		            "          free(p);"                                                    +"\n"+
		            "          p = 0;"                                                     +"\n"+
		            "          return;  //DEFECT"                                          +"\n"+
		            "      }"                                                              +"\n"+
		            "      if (flag == 34) {"                                              +"\n"+
		            "          free(p);"                                                    +"\n"+
		            "          return; //DEFECT"                                           +"\n"+
		            "      }"                                                              +"\n"+
		            "      free(p);"                                                       +"\n"+
		            " }"																  +"\n"+
		            "  void foo()"                                                      +"\n"+
		            "  {"                                                                  +"\n"+
		            "      int *ptr;"                                                      +"\n"+
		            "      ptr = (int*)malloc(sizeof(int));"                               +"\n"+
		            "      my_free(ptr,1); //DEFECT"                                            +"\n"+
		            " }"                                                                   
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
				 },
//////////////////////////2//////////////////////////////////////////////
		            {
		            "#include <stdlib.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_mlf_2_f1(int flag,char *p){"                                   +"\n"+
		            "     if(flag)"                                                        +"\n"+
		            "         free(p);"                                                 +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_mlf_2_f2(int flag)"                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *buf = (char *)malloc(sizeof(char)*10);"                                           +"\n"+
		            ""                                                                     +"\n"+
		            "	zk_mlf_2_f1(flag,buf); //DEFECT"                                     +"\n"+
		            ""                                                                     +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "MLF_FREE"
		            ,
		            },
//////////////////////////3//////////////////////////////////////////////
//xwt:赋值给全局变量这种没有列为创建自动机条件
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "int * i;"                                                             +"\n"+
		            "void f(int* p,int flag){"                                             +"\n"+
		            "   if(flag)"                                                          +"\n"+
		            "      i=p;"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f1(int flag){"                                                   +"\n"+
		            "   int*p =(int*)malloc(10);"                                          +"\n"+
		            "   f(p,flag);"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
//////////////////////////4//////////////////////////////////////////////
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "int * i;"                                                             +"\n"+
		            "void f(int* p,int flag){"                                             +"\n"+
		            "      i=p;"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f1(int flag){"                                                   +"\n"+
		            "   int*p =(int*)malloc(10);"                                          +"\n"+
		            "   f(p,flag);"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },  
//////////////////////////5//////////////////////////////////////////////
					 {
						 "#include <stdlib.h>"                                                  +"\n"+
						 "  void my_free(char *p) {"                                            +"\n"+
						 "      int a;"                                            +"\n"+
						 "      if(a || p)"                                                          +"\n"+
						 "          free(p);"                                                   +"\n"+
						 " }"																    +"\n"+
						 "  void foo()"                                                         +"\n"+
						 "  {"                                                                  +"\n"+
						 "      int *ptr;"                                                      +"\n"+
						 "      ptr = (int*)malloc(sizeof(int));"                               +"\n"+
						 "      my_free(ptr,1); //DEFECT"                                            +"\n"+
						 " }"                                                                   
						 ,
						 "gcc"
				         ,
						 "OK"
						 ,
					 }, 

		 });
	 }
}