package softtest.test.c.gcc.test_team_1;

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
		            "void GHX_BO_1_f1(char p[420])"                                        +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer [400];"                                                  +"\n"+
		            "	strcpy (buffer,\"welcome to beijing \");//FP"                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  1   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "void GHX_BO_1_f1(char p[420])"                                        +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer [400];"                                                  +"\n"+
		            "	strcat (buffer, p);//DEFECT"                                         +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
		        	///////////////// 2  ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <unistd.h>"                                                      +"\n"+
		           // "#include <conio.h>"                                                   +"\n"+
		            "//#include <libgen.h> "                                               +"\n"+
		            "void ghx_bo_8_f8(char *argv[],char a[3],char b[33],char ch)"          +"\n"+
		            "{"                                                                    +"\n"+
		            "FILE *fp;"                                                            +"\n"+
		            "int hand;"                                                            +"\n"+
		            "int i=0;"                                                             +"\n"+
		            " char *password;"                                                     +"\n"+
		            "char string [2];"                                                     +"\n"+
		            " fp = fopen (\"myfile.txt\" , \"r\");"                                    +"\n"+
		            "fgets(string,5,fp);//DEFECT"                                          +"\n"+
		            ""                                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "while((ch = getchar()) != '\\n') "                                     +"\n"+
		            "  { "                                                                 +"\n"+
		            "  if(ch == -1) break; "                                               +"\n"+
		            "  string[i++] = ch; "                                                 +"\n"+
		            "  } "                                                                 +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
		        	///////////////// 3  ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <unistd.h>"                                                      +"\n"+
		            //"#include <conio.h>"                                                   +"\n"+
		            "//#include <libgen.h> "                                               +"\n"+
		            "void ghx_bo_8_f8(char *argv[],char a[3],char b[33],char ch)"          +"\n"+
		            "{"                                                                    +"\n"+
		            "FILE *fp;"                                                            +"\n"+
		            "int hand;"                                                            +"\n"+
		            "int i=0;"                                                             +"\n"+
		            " char *password;"                                                     +"\n"+
		            "char string [2];"                                                     +"\n"+
		            " fp = fopen (\"myfile.txt\" , \"r\");"                                    +"\n"+
		            "fread(string,10,10,fp);//DEFECT"                                      +"\n"+
		            ""                                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "while((ch = getchar()) != '\\n') "                                     +"\n"+
		            "  { "                                                                 +"\n"+
		            "  if(ch == -1) break; "                                               +"\n"+
		            "  string[i++] = ch; "                                                 +"\n"+
		            "  } "                                                                 +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
		        	///////////////// 4  ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <unistd.h>"                                                      +"\n"+
		           // "#include <conio.h>"                                                   +"\n"+
		            "//#include <libgen.h> "                                               +"\n"+
		            "void ghx_bo_8_f8(char *argv[],char a[3],char b[33],char ch)"          +"\n"+
		            "{"                                                                    +"\n"+
		            "FILE *fp;"                                                            +"\n"+
		            "int hand;"                                                            +"\n"+
		            "int i=0;"                                                             +"\n"+
		            " char *password;"                                                     +"\n"+
		            "char string [2];"                                                     +"\n"+
		            " fp = fopen (\"myfile.txt\" , \"r\");"                                    +"\n"+
		            "read(hand,string,20);"                                        +"\n"+
		            ""                                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "while((ch = getchar()) != '\\n') "                                     +"\n"+
		            "  { "                                                                 +"\n"+
		            "  if(ch == -1) break; "                                               +"\n"+
		            "  string[i++] = ch; "                                                 +"\n"+
		            "  } "                                                                 +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
		        	/////////////////  5///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            "void ghx_bo_13_f13(FILE* f, char* x)"                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "char tmp[100];"                                                       +"\n"+
		            ""                                                                     +"\n"+
		            "fscanf(f, \"%10s\", tmp);"                                              +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  6///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            "void ghx_bo_13_f13(FILE* f, char* x)"                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "char tmp[100];"                                                       +"\n"+
		            ""                                                                     +"\n"+
		            "fscanf(f, \"%20s\", tmp);"                                              +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  7///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            "void ghx_bo_13_f13(FILE* f, char* x)"                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "char tmp[100];"                                                       +"\n"+
		            ""                                                                     +"\n"+
		            "fscanf(f, \"%10s\", x);"                                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  8///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            "void ghx_bo_13_f13(FILE* f, char* x)"                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "char tmp[100];"                                                       +"\n"+
		            ""                                                                     +"\n"+
		            "fscanf(f, \"%s\", x);//DEFECT"                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
		        	/////////////////  9///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            "void ghx_bo_13_f13(FILE* f, char* x)"                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "char tmp[100];"                                                       +"\n"+
		            ""                                                                     +"\n"+
		            "fscanf(f, \"%%%s\", x);//DEFECT"                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
		        	/////////////////  10///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            "void ghx_bo_13_f13(FILE* f, char* x)"                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "char tmp[100];"                                                       +"\n"+
		            ""                                                                     +"\n"+
		            "fscanf(f, \"%%%10s\", x);"                                              +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  11///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            "void ghx_bo_13_f13(FILE* f, char* x)"                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "char tmp[100];"                                                       +"\n"+
		            ""                                                                     +"\n"+
		            "fscanf(f, \"%*s%s\", x);//DEFECT"                                       +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
		        	/////////////////  12///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            "void ghx_bo_13_f13(FILE* f, char* x)"                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "char tmp[100];"                                                       +"\n"+
		            ""                                                                     +"\n"+
		            "fscanf(f, \"%*s%10s\", x);"                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  13  ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "void ghx_bo_15_f15()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "char buf [20];"                                                       +"\n"+
		            "char long_src[30];"                                                   +"\n"+
		            "char *external_pointer;"                                              +"\n"+
		            "strncpy(buf, long_src, 30); //DEFECT"                                 +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
		        	/////////////////  14  ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "void ghx_bo_15_f15()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "char buf [20];"                                                       +"\n"+
		            "char long_src[30];"                                                   +"\n"+
		            "char *external_pointer;"                                              +"\n"+
		            "strncpy(buf, external_pointer, sizeof(buf));//DEFECT"                 +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
		        	/////////////////  15  ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "void ghx_bo_15_f15()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "char buf [20];"                                                       +"\n"+
		            "char long_src[30];"                                                   +"\n"+
		            "char *external_pointer;"                                              +"\n"+
		            "strncpy(buf, external_pointer, 30); //DEFECT"                         +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
		        	/////////////////  16  ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "void ghx_bo_15_f15()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "char buf [20];"                                                       +"\n"+
		            "char long_src[30];"                                                   +"\n"+
		            "char *external_pointer;"                                              +"\n"+
		            "strncpy(buf, external_pointer, sizeof(buf)-1); //FP"                  +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  17  ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "int ghx_bo_16_f16()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "char overflown_buf[20];"                                              +"\n"+
		            "gets(overflown_buf);//DEFECT"                                         +"\n"+
		            "return 0;"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
		        	/////////////////  18  ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "int ghx_bo_16_f16()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "char overflown_buf[20];"                                              +"\n"+
		            "gets(overflown_buf+1);//DEFECT"                                       +"\n"+
		            "return 0;"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
		        	/////////////////  19  ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "int ghx_bo_17_f17(char *POINTERbuf)"                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "char FIXEDbuf[12];"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "strcpy(FIXEDbuf, \"Something rather large\");//DEFECT"                  +"\n"+
		            "return 0;"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
		        	/////////////////  20  ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "int ghx_bo_17_f17(char *POINTERbuf)"                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "char FIXEDbuf[12];"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "strcpy(POINTERbuf, \"Something very large as well\");"                  +"\n"+
		            "return 0;"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  21  ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            "void jhb_bo_1_f1(){"                                                  +"\n"+
		            "	char *strPathName = (char*)malloc(100*sizeof(char));"                +"\n"+
		            "	char s[3];"                                                          +"\n"+
		            "	strcpy(strPathName,\"\\\\Application\\\\MakeSheet\\\\*.pms\");  //FT"        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  22  ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            "void jhb_bo_1_f1(){"                                                  +"\n"+
		            "	char *strPathName = (char*)malloc(100*sizeof(char));"                +"\n"+
		            "	char s[3];"                                                          +"\n"+
		            "	strcpy(s,\"\\\\\\\\\");  //FP"                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  23  ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            "void jhb_bo_1_f1(){"                                                  +"\n"+
		            "	char *strPathName = (char*)malloc(100*sizeof(char));"                +"\n"+
		            "	char s[3];"                                                          +"\n"+
		            "	strcpy(s,\"\\\\\\\\\\\\*.*\");  //DEFECT"                                    +"\n"+
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

