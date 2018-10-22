package softtest.test.gcc.rules.safety;

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
/**
 * 
 * @author liuyan
 *
 */
@RunWith(Parameterized.class)
public class Test_UCKRET extends ModelTestBase
{

	public Test_UCKRET(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

//	@Override
//	public void initFSM()
//	{
//		fsm = "softtest/rules/cpp/safety/UCKRET-0.1.xml";
//	}
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/safety/UCKRET-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("safety");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
		
		//加载库函数摘要
		LIB_SUMMARYS_PATH="gcc_lib/unck-ret-value_summary.xml";
//		libManager.loadLib(LIB_SUMMARYS_PATH);
		libManager.loadSingleLibFile(LIB_SUMMARYS_PATH);
		Set<MethodNameDeclaration> libDecls = libManager.compileLib(pre.getLibIncludes());
		interContext = InterContext.getInstance();
		interContext.addLibMethodDecl(libDecls);
	}
	@Parameters
	 public static Collection<Object[]> testcaseAndResults()
	 {
		 return Arrays.asList(
				 new Object[][]
				 {
////////////////////////////0//////////////////////////////////////////////
				            {
				            ""                                                                     +"\n"+
				            "#include <stdlib.h>"                                                  +"\n"+
				            "#include <stdio.h>"                                                   +"\n"+
				            ""                                                                     +"\n"+
				            "int yxh_UCKRET_f_1 ()"                                                +"\n"+
				            "{"                                                                    +"\n"+
				            "	int *p;"                                                             +"\n"+
				            "	if ((p = (int *)malloc(4)) != NULL)"                                 +"\n"+
				            "	{"                                                                   +"\n"+
				            "		*p = 4;"                                                            +"\n"+
				            "	}"                                                                   +"\n"+
				            "	"                                                                    +"\n"+
				            "	return 0;"                                                           +"\n"+
				            "}"   
				            ,
				            "gcc"
				            ,
				            "OK"
				            ,
				            },
////////////////////////////1/////////////////////////////////////////////
				            {
				            ""                                                                     +"\n"+
				            "#include <stdlib.h>"                                                  +"\n"+
				            "#include <stdio.h>"                                                   +"\n"+
				            ""                                                                     +"\n"+
				            "void yxh_UCKRET_2_f1 ()"                                              +"\n"+
				            "{"                                                                    +"\n"+
				            "	char* s=(char*)malloc(1);"                                           +"\n"+
				            "	if (!s)"                                                             +"\n"+
				            "		return;"                                                            +"\n"+
				            "}"    
				            ,
				            "gcc"
				            ,
				            "OK"
				            ,
				            },
/////////////////////////2//////////////////////////////////////////////
				            {
				            ""                                                                     +"\n"+
				            "#include <stdio.h>"                                                   +"\n"+
				            "#include <stdlib.h>"                                                  +"\n"+
				            "#include <string.h>"                                                  +"\n"+
				            ""                                                                     +"\n"+
				            "int main()"                                                           +"\n"+
				            "{"                                                                    +"\n"+
				            "    char *buf;"                                                       +"\n"+
				            "    int req_size = 10;"                                               +"\n"+
				            "    char xfer[10];"                                                   +"\n"+
				            "    "                                                                 +"\n"+
				            "    buf = (char*) malloc(req_size);"                                  +"\n"+
				            "    strncpy(buf, xfer, req_size); //DEFECT, UCKRET"                   +"\n"+
				            "    "                                                                 +"\n"+
				            "    return 0;"                                                        +"\n"+
				            "}"   
				            ,
				            "gcc"
				            ,
				            "UCKRET"
				            ,
				            },
////////////////////////3////////////////////////////////////////	
				            {
				            "#include <string.h>"                                                  +"\n"+
				            "#include <stdlib.h>"                                                  +"\n"+
				            "int ghx_uckret_1_f1()"                                                +"\n"+
				            "{"                                                                    +"\n"+
				            "	char *buf;"                                                          +"\n"+
				            "	char *xfer=\"abc\";"                                                   +"\n"+
				            "	int req_size=10;"                                                    +"\n"+
				            "buf = (char*) malloc(req_size);//DEFECT"                              +"\n"+
				            "strncpy(buf, xfer, req_size);"                                        +"\n"+
				            "return 0;"                                                            +"\n"+
				            "}" 
				            ,
				            "gcc"
				            ,
				            "UCKRET"
				            ,
				            },
////////////////////////////4//////////////////////////////////////////////
						 {
					            "#include <stdio.h>"                                                   +"\n"+
					            "#include <stdlib.h>"                                                  +"\n"+
					            "#include <string.h>"                                                  +"\n"+
					            ""                                                                     +"\n"+
					            "int ghx_uckret_2_f2(int argc, char *argv[])"                          +"\n"+
					            "{"                                                                    +"\n"+
					            "int i=0,j=0;"                                                         +"\n"+
					            "printf(\"Enter two numbers:\\n\");"                                      +"\n"+
					            "scanf(\"%d %d\", &i, &j);//DEFECT"                                      +"\n"+
					            "printf (\"Result = %d\\n\", i / j);"                                     +"\n"+
					            "return 0;"                                                            +"\n"+
					            "}"                                                                    +"\n"+
					            ""                                                                     +"\n"+
					            ""                                                                     +"\n"+
					            "int ghx_uckret_2_f1(int argc, char *argv[])"                          +"\n"+
					            "{"                                                                    +"\n"+
					            "unsigned int i=0,j=0;"                                                +"\n"+
					            "unsigned int result = 0;"                                             +"\n"+
					            "printf(\"Enter two numbers:\\n\");"                                      +"\n"+
					            "result = scanf(\"%d %d\", &i, &j);"                                     +"\n"+
					            "if (result != 2)//FP"                                                 +"\n"+
					            " {"                                                                   +"\n"+
					            "printf (\"Error"
					            + ", you should enter two numbers!\\n\");      "             +"\n"+
					            "return 1;"                                                            +"\n"+
					            "}              "                                                      +"\n"+
					            "printf (\"Result = %d\\n\", i / j);"                                     +"\n"+
					            "return 0;"                                                            +"\n"+
					            "}"                                                                    
					            ,
				            	"gcc"
					            ,
					            "UCKRET"
					            ,
						 		},
////////////////////////////5//////////////////////////////////////////////
				            {
				            "#include <stdlib.h>"                                                  +"\n"+
				            "	 "                                                                   +"\n"+
				            "int ghx_uckret_4_f4 ()"                                               +"\n"+
				            "{"                                                                    +"\n"+
				            "malloc(sizeof(int)*4);//DEFECT"                                       +"\n"+
				            "/* If a functions return value is not checked, it could have failed without any warning. */"+"\n"+
				            "return 0;"                                                            +"\n"+
				            "}"   
				            ,
				            "gcc"
				            ,
				            "UCKRET"
				            ,
				            },
////////////////////////6//////////////////////////////////////////////	
				            {
				            "#include <string.h>"                                                  +"\n"+
				            "#include <stdlib.h>"                                                  +"\n"+
				            "f(){"                                                                 +"\n"+
				            "	char* s[4];"                                                         +"\n"+
				            "	s[1]=(char*)malloc(12);"                                             +"\n"+
				            "	if(!s[1])"                                                           +"\n"+
				            "		return;"                                                            +"\n"+
				            "}"    
				            ,
				            "gcc"
				            ,
				            "OK"
				            ,
				            },
////////////////////////7//////////////////////////////////////////////	
				            {
				                "#include<stdlib.h>"                                                   +"\n"+
				                "#include<stdio.h>"                                                    +"\n"+
				                "void func(){"                                                         +"\n"+
				                "	char *textptr;"                                                      +"\n"+
				                "	char *textinfo;"                                                     +"\n"+
				                "	textptr=textinfo=(char *)malloc(1);"                                 +"\n"+
				                "	return;"                                                             +"\n"+
				                "}"                                                                        
					            ,
					            "gcc"
					            ,
					            "UCKRET"
					            ,
					            }
				 });
	 }

}
