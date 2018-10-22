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
public class NPD_PRE extends ModelTestBase {
	public NPD_PRE(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/NPD_PRE-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("fault");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
		
		//加载库函数摘要
		LIB_SUMMARYS_PATH="gcc_lib/npd_summary.xml";
		libManager.loadSingleLibFile(LIB_SUMMARYS_PATH);
		libManager.loadSingleLibFile("gcc_lib/lib_summary.xml");
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
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(char *);"                                                  +"\n"+
		            "void f(int, char*);"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void func1(int flag)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *ptr = NULL;"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "	ptr = (char*)malloc(sizeof(char));"                                  +"\n"+
		            "	f(flag,ptr); //DEFECT"                                               +"\n"+
		            "	if (ptr)"                                                            +"\n"+
		            "	{"                                                                   +"\n"+
		            "		free(ptr);"                                                         +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f(int flag,char* var)"                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "	if(flag) {"                                                          +"\n"+
		            "    	func2(var);"                                                     +"\n"+
		            "    } else {"                                                         +"\n"+
		            "		*var = 3;"                                                          +"\n"+
		            "    }"                                                                +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(char *var)"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "	*var = 2;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
	/////////////////  1  ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(char *);"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void func1()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	func2(NULL); //DEFECT"                                               +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(char *var)"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "	*var = 2; "                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
	/////////////////  2   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "int g_val = 1;"                                                       +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int, char *);"                                             +"\n"+
		            "void func3(char *, int);"                                             +"\n"+
		            "void func4(int, char *, int);"                                        +"\n"+
		            ""                                                                     +"\n"+
		            "void func1()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *ptr;"                                                          +"\n"+
		            ""                                                                     +"\n"+
		            "	ptr = NULL;"                                                         +"\n"+
		            "	func2(1, ptr); //DEFECT"                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int val, char *var)"                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "	func3(var, val);"                                                    +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func3(char *var, int val)"                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "	func4(val, var, g_val);"                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func4(int val, char *var, int flag)"                             +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (flag > 0) {"                                                     +"\n"+
		            "		*var = val;"                                                        +"\n"+
		            "	} else {"                                                            +"\n"+
		            "		return;"                                                            +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
	/////////////////  3   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "struct s_val {"                                                       +"\n"+
		            "	int i;"                                                              +"\n"+
		            "	int j;"                                                              +"\n"+
		            "};"                                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int, struct s_val *);"                                     +"\n"+
		            "void func3(struct s_val *, int);"                                     +"\n"+
		            "void func4(int, struct s_val *, int);"                                +"\n"+
		            ""                                                                     +"\n"+
		            "void func1()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	func2(1, NULL); //DEFECT"                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int val, struct s_val *var)"                               +"\n"+
		            "{"                                                                    +"\n"+
		            "	func3(var, val);"                                                    +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func3(struct s_val *var, int val)"                               +"\n"+
		            "{"                                                                    +"\n"+
		            "	func4(val, var, 1);"                                                 +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func4(int val, struct s_val *var, int flag)"                     +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (flag > 0) {"                                                     +"\n"+
		            "		var->i = val;"                                                      +"\n"+
		            "	} else {"                                                            +"\n"+
		            "		return;"                                                            +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },

	/////////////////  4   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(float*);"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void func1()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	float *ptr = NULL;"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "	ptr = (float*)malloc(sizeof(float));"                                +"\n"+
		            "	func2(ptr); //DEFECT"                                                +"\n"+
		            "	if (ptr)"                                                            +"\n"+
		            "	{"                                                                   +"\n"+
		            "		free(ptr);"                                                         +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(float *var)"                                               +"\n"+
		            "{"                                                                    +"\n"+
		            "	*var = 0.1f;"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
	/////////////////  5   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "int g_val = 1;"                                                       +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int, double*);"                                            +"\n"+
		            "void func3(double*, int);"                                            +"\n"+
		            "void func4(int, double*, int);"                                       +"\n"+
		            ""                                                                     +"\n"+
		            "void func1()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	double *ptr;"                                                        +"\n"+
		            ""                                                                     +"\n"+
		            "	ptr = NULL;"                                                         +"\n"+
		            "	func2(1, ptr); //DEFECT"                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int val, double *var)"                                     +"\n"+
		            "{"                                                                    +"\n"+
		            "	func3(var, val);"                                                    +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func3(double *var, int val)"                                     +"\n"+
		            "{"                                                                    +"\n"+
		            "	func4(val, var, g_val);"                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func4(int val, double *var, int flag)"                           +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (flag > 0) {"                                                     +"\n"+
		            "		*var = val;"                                                        +"\n"+
		            "	} else {"                                                            +"\n"+
		            "		return;"                                                            +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },

	/////////////////  6   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void func3(int *var)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	*var = 1;"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2(int *var)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	func3(var);"                                                         +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "void func1(int flag)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	int *ptr = 0;"                                                       +"\n"+
		            ""                                                                     +"\n"+
		            "	if (flag > 0) {"                                                     +"\n"+
		            "		ptr = (int*)malloc(sizeof(int));"                                   +"\n"+
		            "	}"                                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "	func2(ptr); //DEFECT"                                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  7   ///////////////////	
			          //hcj函数返回值取不着
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "char* ghx_npd_1_f1(int b)"                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	if(b)"                                                               +"\n"+
		            "		return NULL;"                                                       +"\n"+
		            "	return (char*)malloc(10);"                                           +"\n"+
		            "}"                                                                    +"\n"+
		            "void ghx_npd_1_f2(char* p)"                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "	char a=*p;"                                                          +"\n"+
		            "}"                                                                    +"\n"+
		            "void ghx_npd_1_f3(int a)"                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *p=ghx_npd_1_f1(a);"                                            +"\n"+
		            "	ghx_npd_1_f2(p);  //defect"                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },       
		        	/////////////////  8   ///////////////////
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "#include <string.h>"                                                  +"\n"+
		            "#include <io.h>"                                                      +"\n"+
		            "#include  <unistd.h>"                                                      +"\n"+
		            "struct ghx_npd_1_s1"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *ss;"                                                           +"\n"+
		            "};"                                                                   +"\n"+
		            "void ghx_npd_1_f1()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	struct ghx_npd_1_s1 *s;"                                             +"\n"+
		            "	s=(struct ghx_npd_1_s1*)malloc(sizeof(ghx_npd_1_s1));"               +"\n"+
		            "	read(1,s,sizeof(s));//DEFECT"                                        +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  9   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "char ghx_npd_11_f11()"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *ptr=NULL;"                                                     +"\n"+
		            "	char *ph;"                                                           +"\n"+
		            "	int i=1;"                                                            +"\n"+
		            "    ph=(char *)memchr(ptr,'p',10);//DEFECT"                           +"\n"+
		            "    ph[i]=0;//DEFECT"                                                 +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "int ghx_npd_11_f10 ()"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "  char * pch;"                                                        +"\n"+
		            "  char str[] = \"Example string\";"                                     +"\n"+
		            "  int i=1;"                                                           +"\n"+
		            "  pch = (char*) memchr (str, 'p', strlen(str));//FP"                  +"\n"+
		            "  if (pch!=NULL)"                                                     +"\n"+
		            "    printf (\"'p' found at position %d.\\n\", pch-str+1);"               +"\n"+
		            "  else"                                                               +"\n"+
		            "    pch[i]=0;//FP"                                                    +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  10   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "int ghx_npd_12_f12 (int len1,int len2)"                               +"\n"+
		            "{"                                                                    +"\n"+
		            "  char *str1=NULL;"                                                   +"\n"+
		            "  char *str2=NULL;"                                                   +"\n"+
		            "  int n;"                                                             +"\n"+
		            ""                                                                     +"\n"+
		            "  n=memcmp ( str1, str2, len1>len2?len1:len2 );//DEFECT"              +"\n"+
		            "  if (n>0) printf (\"'%s' is greater than '%s'.\\n\",str1,str2);"        +"\n"+
		            "  else if (n<0) printf (\"'%s' is less than '%s'.\\n\",str1,str2);"      +"\n"+
		            "  else printf (\"'%s' is the same as '%s'.\\n\",str1,str2);"             +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "int ghx_npd_12_f11 ()"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "  char str1[]=\"abcdefg\";"                                             +"\n"+
		            "  char str2[]=\"abc\";"                                                 +"\n"+
		            "  int n;"                                                             +"\n"+
		            "  int len1, len2;"                                                    +"\n"+
		            "  len1=strlen(str1);"                                                 +"\n"+
		            "  len2=strlen(str2);"                                                 +"\n"+
		            "  n=memcmp ( str1, str2, len1>len2?len1:len2 );//FP"                  +"\n"+
		            "  if (n>0) printf (\"'%s' is greater than '%s'.\\n\",str1,str2);"        +"\n"+
		            "  else if (n<0) printf (\"'%s' is less than '%s'.\\n\",str1,str2);"      +"\n"+
		            "  else printf (\"'%s' is the same as '%s'.\\n\",str1,str2);"             +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  11   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "int ghx_npd_13_f13(char *str5,char*str6)"                             +"\n"+
		            "{"                                                                    +"\n"+
		            "char *str1=NULL;"                                                     +"\n"+
		            "char *str2=NULL;"                                                     +"\n"+
		            "char *str3=\"abcedfg\";"                                                +"\n"+
		            "char *str4[40];"                                                      +"\n"+
		            "memcpy(str1,str3,7);  //DEFECT"                                       +"\n"+
		            "memcpy(str4,str2,10);  //DEFECT"                                      +"\n"+
		            "memcpy(str5,str6,strlen(str6)); //DEFECT"                             +"\n"+
		            "return 0;"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int ghx_npd_13_f12 ()"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "  char str1[]=\"Sample string\";"                                       +"\n"+
		            "  char str2[40];"                                                     +"\n"+
		            "  char str3[40];"                                                     +"\n"+
		            "  memcpy (str2,str1,strlen(str1)+1);//FP"                             +"\n"+
		            "  memcpy (str3,\"copy successful\",16);//FP"                            +"\n"+
		            "  printf (\"str1: %s\\nstr2: %s\\nstr3: %s\\n\",str1,str2,str3);"          +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  12   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "int ghx_npd_15_f15()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "char *str=NULL;"                                                      +"\n"+
		            "memset(str,'*',6);//DEFECT"                                           +"\n"+
		            "return 0;"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int ghx_npd_15_f14()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "char str[]=\"welcome to beijing\";"                                     +"\n"+
		            "memset(str,'*',7);//FP"                                               +"\n"+
		            "printf(\"%s\\n\",str);"                                                  +"\n"+
		            "return 0;"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
	/////////////////  13   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <math.h>"                                                    +"\n"+
		            "int ghx_npd_17_f17() "                                                +"\n"+
		            "{ "                                                                   +"\n"+
		            "double fraction;"                                                     +"\n"+
		            "double *integer=NULL; "                                               +"\n"+
		            "double number = 100000.567; "                                         +"\n"+
		            "fraction = modf(number, integer); //DEFECT"                           +"\n"+
		            "return 0; "                                                           +"\n"+
		            "} "                                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "int ghx_npd_17_f16() "                                                +"\n"+
		            "{ "                                                                   +"\n"+
		            "double fraction, integer; "                                           +"\n"+
		            "double number = 100000.567; "                                         +"\n"+
		            "fraction = modf(number, &integer); //FP"                              +"\n"+
		            "printf(\"The whole and fractional parts of %lf are %lf and %lf\\n\", number, integer, fraction); "                                         +"\n"+
		            ""                                                                     +"\n"+
		            "return 0; "                                                           +"\n"+
		            "} "                                                                   
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
	/////////////////  14   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "int ghx_npd_19_f19()"                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "   FILE *fp;"                                                         +"\n"+
		            "   fp = fopen(\"perror.dat\", \"r\");"                                    +"\n"+
		            ""                                                                     +"\n"+
		            "      perror(fp);//DEFECT"                                            +"\n"+
		            "   return 0;"                                                         +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
	/////////////////  15   ///////////////////
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "int ghx_npd_20_f20 ()"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "  FILE * pFile;"                                                      +"\n"+
		            "  char c;"                                                            +"\n"+
		            ""                                                                     +"\n"+
		            "  pFile=fopen(\"alphabet.txt\",\"wt\");"                                  +"\n"+
		            "    for (c = 'A' ; c <= 'Z' ; c++)"                                   +"\n"+
		            "    {"                                                                +"\n"+
		            "    putc (c , pFile);//DEFECT"                                        +"\n"+
		            "    }"                                                                +"\n"+
		            "  fclose (pFile); //DEFECT"                                           +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int ghx_npd_20_f19()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "FILE * pFile;"                                                        +"\n"+
		            "  char c;"                                                            +"\n"+
		            ""                                                                     +"\n"+
		            "  pFile=fopen(\"alphabet.txt\",\"wt\");"                                  +"\n"+
		            "    for (c = 'A' ; c <= 'Z' ; c++)"                                   +"\n"+
		            "	{"                                                                   +"\n"+
		            "		if(pFile!=NULL)"                                                    +"\n"+
		            "		{"                                                                  +"\n"+
		            "		putc(c,pFile);//FP"                                                 +"\n"+
		            "		fclose(pFile);"                                                     +"\n"+
		            "		}"                                                                  +"\n"+
		            "	}"                                                                   +"\n"+
		            "		return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  16   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_32_f1(int num, int *ptr)"                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	*ptr = num;"                                                         +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_32_f2()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	int val = 32;"                                                       +"\n"+
		            "	int *ptr;"                                                           +"\n"+
		            ""                                                                     +"\n"+
		            "	ptr = (int *)malloc(sizeof(int));"                                   +"\n"+
		            "	zk_npd_32_f1(val, ptr); //DEFECT"                                    +"\n"+
		            ""                                                                     +"\n"+
		            "	if (ptr)"                                                            +"\n"+
		            "		free(ptr);"                                                         +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  17   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_35_f1()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *key;"                                                          +"\n"+
		            ""                                                                     +"\n"+
		            "	key = (char *)malloc(sizeof(char)*10);"                              +"\n"+
		            "	sprintf(key, \"char\"); //DEFECT"                                      +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  18   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_31_f1(char *pathname)"                                    +"\n"+
		            "{"                                                                    +"\n"+
		            "	FILE *fp;"                                                           +"\n"+
		            ""                                                                     +"\n"+
		            "	fp = fopen(pathname, \"a\");"                                          +"\n"+
		            "	fprintf(fp, \"Acess file\"); //DEFECT"                                 +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  19   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_21_f1()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *ptr;"                                                          +"\n"+
		            ""                                                                     +"\n"+
		            "	ptr = tmpnam(NULL); //FP"                                            +"\n"+
		            "	printf(\"Tmpname: %s\", ptr);"                                         +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  20   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_19_f1(char c)"                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	FILE *fp = NULL;"                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "	ungetc(c, fp); //DEFECT"                                             +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_19_f2(FILE *fp)"                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (fp == NULL)"                                                     +"\n"+
		            "		return;"                                                            +"\n"+
		            "	ungetc((int)'a', fp); //FP"                                          +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  21   ///////////////////
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_18_f1()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	FILE *fp;"                                                           +"\n"+
		            ""                                                                     +"\n"+
		            "	fp = tmpfile();"                                                     +"\n"+
		            "	fputc((int)'a', fp); //DEFECT"                                       +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_18_f2()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	FILE *fp;"                                                           +"\n"+
		            "	fp = tmpfile();"                                                     +"\n"+
		            "	if (fp != NULL)"                                                     +"\n"+
		            "		fputc((int)'a', fp); //FP"                                          +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  22   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_17_f1()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *des = NULL;"                                                   +"\n"+
		            "	char *src = NULL;"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "	strxfrm(des, src, 5); //DEFECT"                                      +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_17_f2()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	char des[10];"                                                       +"\n"+
		            "	char src[] = \"sample\";"                                              +"\n"+
		            ""                                                                     +"\n"+
		            "	strxfrm(des, src, sizeof(src)); //FP"                                +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  23   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_15_f1()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *str = NULL;"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "	strtoul(str, NULL, 2); //DEFECT"                                     +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_15_f2()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	char str[] = \"2009 123\";"                                            +"\n"+
		            ""                                                                     +"\n"+
		            "	strtoul(str, NULL, 10); //FP"                                        +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  24   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_14_f1()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	char str[] = \"This is a sample\";"                                    +"\n"+
		            "	char *pch;"                                                          +"\n"+
		            ""                                                                     +"\n"+
		            "	pch = strtok(str, NULL); //DEFECT"                                   +"\n"+
		            "	printf(\"%s\", pch); //DEFECT"                                         +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_14_f2()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	char str[] = \"This is a sample\";"                                    +"\n"+
		            "	char *pch;"                                                          +"\n"+
		            ""                                                                     +"\n"+
		            "	pch = strtok(str, \" \"); //FP"                                        +"\n"+
		            "	while (pch != NULL)"                                                 +"\n"+
		            "	{"                                                                   +"\n"+
		            "		printf(\"%s\", pch); //FP"                                            +"\n"+
		            "		strtok(NULL, \" \"); //FP"                                            +"\n"+
		            "	}"                                                                   +"\n"+
		            "	printf(\"%s\", pch); //DEFECT"                                         +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },   
		        	/////////////////  25   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_12_f1()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *str = NULL;"                                                   +"\n"+
		            "	char *sub = NULL;"                                                   +"\n"+
		            "	char *pch;"                                                          +"\n"+
		            ""                                                                     +"\n"+
		            "	pch = strstr(str, sub); //DEFECT"                                    +"\n"+
		            "	if (pch)"                                                            +"\n"+
		            "		printf(\"%s\", pch); //FP"                                            +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_12_f2()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	char str[] = \"This is sample\";"                                      +"\n"+
		            "	char *pch;"                                                          +"\n"+
		            ""                                                                     +"\n"+
		            "	pch = strstr(str, \"nothing\"); //FP"                                  +"\n"+
		            "	printf(\"%s\", pch); //DEFECT"                                         +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  26   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "char *zk_npd_11_g1 = NULL;"                                           +"\n"+
		            "char *zk_npd_11_g2 = NULL;"                                           +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_11_f1()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	strspn(zk_npd_11_g1, zk_npd_11_g2); //DEFECT"                        +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_11_f2()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (zk_npd_11_g1 && zk_npd_11_g2)"                                   +"\n"+
		            "		strspn(zk_npd_11_g1, zk_npd_11_g2); //FP"                           +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  27   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_10_f1()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *str = NULL;"                                                   +"\n"+
		            "	char *pch;"                                                          +"\n"+
		            ""                                                                     +"\n"+
		            "	pch = strrchr(str, 's'); //DEFECT"                                   +"\n"+
		            "	printf(\"%c\", *pch); //DEFECT"                                        +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_10_f2()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	char str[] = \"This is a sample\";"                                    +"\n"+
		            "	char *pch;"                                                          +"\n"+
		            ""                                                                     +"\n"+
		            "	pch = strrchr(str, 's'); //FP"                                       +"\n"+
		            "	if (pch)"                                                            +"\n"+
		            "		printf(\"%c\", *pch); //FP"                                           +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  28   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_9_f1()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *str1, *str2;"                                                  +"\n"+
		            "	str1 = NULL;"                                                        +"\n"+
		            "	str2 = NULL;"                                                        +"\n"+
		            ""                                                                     +"\n"+
		            "	strpbrk(str1, str2); //DEFECT"                                       +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_9_f2()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *pch;"                                                          +"\n"+
		            "	char str[] = \"This is sample\";"                                      +"\n"+
		            "	char key[] = \"xyz\";"                                                 +"\n"+
		            ""                                                                     +"\n"+
		            "	pch = strpbrk(str, key); //FP"                                       +"\n"+
		            "	printf(\"%c\", *pch); //DEFECT"                                        +"\n"+
		            ""                                                                     +"\n"+
		            "	if (pch)"                                                            +"\n"+
		            "		printf(\"%c\", *pch); //FP"                                           +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  29   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_8_f1()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *des = NULL;"                                                   +"\n"+
		            "	char *src = NULL;"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "	strncpy(des, src, 4); //DEFECT"                                      +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_8_f2()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char des[10];"                                                       +"\n"+
		            "	char src[] = \"This is a sample\";"                                    +"\n"+
		            ""                                                                     +"\n"+
		            "	strncpy(des, src, 7); //FP"                                          +"\n"+
		            "	des[7] = '\\0';"                                                      +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  30   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_7_f1()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *str1 = NULL;"                                                  +"\n"+
		            "	char *str2 = NULL;"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "	strncmp(str1, str2, 5); //DEFECT"                                    +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_7_f2()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *str1 = \"hello world\";"                                         +"\n"+
		            "	char *str2 = \"hello\";"                                               +"\n"+
		            ""                                                                     +"\n"+
		            "	strncmp(str1, str2, 5); //FP"                                        +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  31   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_6_f1()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *des = NULL;"                                                   +"\n"+
		            "	char *src = NULL;"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "	strncat(des, src, 4); //DEFECT"                                      +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_6_f2()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char des[10] = \"This\";"                                              +"\n"+
		            "	char src[10] = \"is it and\";"                                         +"\n"+
		            ""                                                                     +"\n"+
		            "	strncat(des, src, 5); //FP"                                          +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  32   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_5_f1(char *str)"                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	strlen(str); //DEFECT"                                               +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_5_f2(char *str)"                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (!str)"                                                           +"\n"+
		            "		return;"                                                            +"\n"+
		            "	strlen(str); //FP"                                                   +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  33   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_3_f1()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *str1 = NULL;"                                                  +"\n"+
		            "	char *str2 = NULL;"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "	strcspn(str1, str2); //DEFECT"                                       +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_3_f2()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *str1 = \"abcdefg\";"                                             +"\n"+
		            "	char *str2 = \"gh\";"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "	strcspn(str1, str2); //FP"                                           +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  34   ///////////////////	
		          //hcj区间运算问题
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "#define MAXSIZE 1024"                                                 +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_2_f1()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *str1 = NULL;"                                                  +"\n"+
		            "	char *str2 = (char*)malloc(MAXSIZE);"                                +"\n"+
		            ""                                                                     +"\n"+
		            "	if (!str2)"                                                          +"\n"+
		            "		return;"                                                            +"\n"+
		            "	strcpy(str2, str1); //DEFECT"                                        +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_2_f2(char *str1, char *str2)"                             +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (!str1 || !str2)"                                                 +"\n"+
		            "		return;"                                                            +"\n"+
		            "	strcpy(str1, str2);"                                                 +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  35   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "int ghx_npd_14_f14()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "char *str1=NULL;"                                                     +"\n"+
		            "char *str2=NULL;"                                                     +"\n"+
		            "memmove(str1,str2,10);//DEFECT"                                       +"\n"+
		            "return 0;"                                                            +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int ghx_npd_14_f13()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "char *dest = \"abcdefghijklmnopqrstuvwxyz0123456789\"; "                +"\n"+
		            "char *src = \"******************************\"; "                       +"\n"+
		            ""                                                                     +"\n"+
		            "memmove(dest, src, 26); //FP"                                         +"\n"+
		            "printf(\"%s\\n\", dest); "                                               +"\n"+
		            "return 0; "                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  36   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "int ghx_npd_21_f21 ()"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "  char *string = NULL;"                                               +"\n"+
		            "  puts (string);//DEFECT"                                             +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int ghx_npd_21_f20()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "char *string=\"welcome to beijing\";"                                   +"\n"+
		            "puts (string);//FP"                                                   +"\n"+
		            "return 0;"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  37   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "int ghx_npd_22_f22 ()"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "  char *str=NULL;"                                                    +"\n"+
		            "  strcat (str,\"strings \");//DEFECT"                                   +"\n"+
		            ""                                                                     +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "int ghx_npd_22_f21 ()"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "  char str[80];"                                                      +"\n"+
		            "  strcpy (str,\"these \");//FP"                                         +"\n"+
		            "  strcat (str,\"strings \");//FP"                                       +"\n"+
		            "  strcat (str,\"are \");//FP"                                           +"\n"+
		            "  strcat (str,\"concatenated.\");//FP"                                  +"\n"+
		            "  puts (str);"                                                        +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  38   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "int ghx_npd_23_f23 ()"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "  char *buffer =NULL;"                                                +"\n"+
		            "  int n, a=5, b=3;"                                                   +"\n"+
		            "  n=sprintf (buffer, \"%d plus %d is %d\", a, b, a+b);//DEFECT"         +"\n"+
		            ""                                                                     +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  39   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "int ghx_npd_24_f24(void)"                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "   char *file=NULL; "                                                 +"\n"+
		            "  remove(file); //DEFECT"                                             +"\n"+
		            "   return 0;"                                                         +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
	/////////////////  40   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "int ghx_npd_25_f25 ()"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "  char *s =NULL;"                                                     +"\n"+
		            "  char str [20];"                                                     +"\n"+
		            "  int i;"                                                             +"\n"+
		            ""                                                                     +"\n"+
		            "  sscanf (s,\"%s %*s %d\",str,&i);//DEFECT"                             +"\n"+
		            "  printf (\"%s -> %d\\n\",str,i);"                                       +"\n"+
		            "  "                                                                   +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
	/////////////////  41   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "int ghx_npd_26_f26 ()"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "  char *str = NULL;"                                                  +"\n"+
		            "  char * pch;"                                                        +"\n"+
		            "  int i=1;"                                                           +"\n"+
		            "  pch=strchr(str,'s');//DEFECT"                                       +"\n"+
		            "  pch[i]=0;//DEFECT"                                                  +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
	/////////////////  42   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "int ghx_npd_27_f27 ()"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "  char *s1 = NULL;"                                                   +"\n"+
		            "  char *s2=NULL;"                                                     +"\n"+
		            "  int ptr;"                                                           +"\n"+
		            "  ptr=strcmp (s1,s2) ;//DEFECT"                                       +"\n"+
		            ""                                                                     +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
	/////////////////  43   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void func()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	FILE *fp;"                                                           +"\n"+
		            ""                                                                     +"\n"+
		            "	fp = fopen(\"myfile.txt\", \"w\");"                                      +"\n"+
		            "	rewind(fp); //DEFECT"                                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
	/////////////////  44   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void func()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	FILE *fp;"                                                           +"\n"+
		            ""                                                                     +"\n"+
		            "	fp = fopen(\"myfile.txt\", \"w\");"                                      +"\n"+
		            "	setvbuf(fp, NULL, _IOFBF, 1024);//DEFECT"                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  45   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void func()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	int i = 1;"                                                          +"\n"+
		            "	char *ptr;"                                                          +"\n"+
		            ""                                                                     +"\n"+
		            "	ptr = (char*)malloc(i+1);"                                           +"\n"+
		            "	memchr(ptr,'p',10); //DEFECT"                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  46   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void func()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *ptr = NULL;"                                                   +"\n"+
		            "	int i = 1, j = 2;"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "	sprintf (ptr, \"%d plus %d is %d\", i, j, i+j);//DEFECT"               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  47   ///////////////////	
		            {
		            "#include <time.h>"                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	mktime(NULL); //DEFECT"                                              +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
	/////////////////  48   ///////////////////	
		            {
		            "#include <time.h>"                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	localtime(NULL); //DEFECT"                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  49   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void func()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *ptr = NULL;"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "	perror(ptr); //DEFECT"                                               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
	/////////////////  50   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void func()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *ptr1 = NULL;"                                                  +"\n"+
		            "	char *ptr2 = NULL;"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "	memcmp(ptr1, ptr2, 1); //DEFECT"                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },

		        	/////////////////  51   ///////////////////	
		        		            {
		        		            "#include <string.h>"                                                  +"\n"+
		        		            ""                                                                     +"\n"+
		        		            "void func()"                                                          +"\n"+
		        		            "{"                                                                    +"\n"+
		        		            "	char *ptr1 = NULL;"                                                  +"\n"+
		        		            "	char *ptr2 = NULL;"                                                  +"\n"+
		        		            ""                                                                     +"\n"+
		        		            "	memmove(ptr1, ptr2, 10); //DEFECT"                                   +"\n"+
		        		            "}"                                                                    
		        		            ,
		        		            "gcc"
		        		            ,
		        		            "NPD_PRE"
		        		            ,
		        		            },
		        	/////////////////  52   ///////////////////	
		        		            {
		        		            "#include <stdio.h>"                                                   +"\n"+
		        		            ""                                                                     +"\n"+
		        		            "void func()"                                                          +"\n"+
		        		            "{"                                                                    +"\n"+
		        		            "	char *ptr1 = NULL;"                                                  +"\n"+
		        		            "	char *ptr2 = NULL;"                                                  +"\n"+
		        		            ""                                                                     +"\n"+
		        		            "	rename(ptr1, ptr2); //DEFECT"                                        +"\n"+
		        		            "}"                                                                    
		        		            ,
		        		            "gcc"
		        		            ,
		        		            "NPD_PRE"
		        		            ,
		        		            },
		        		        	/////////////////  53   ///////////////////	
		        		            {
		        		            "#include <stdio.h>"                                                   +"\n"+
		        		            ""                                                                     +"\n"+
		        		            "void func()"                                                          +"\n"+
		        		            "{"                                                                    +"\n"+
		        		            "	char *ptr1 = NULL;"                                                  +"\n"+
		        		            "	char *ptr2 = NULL;"                                                  +"\n"+
		        		            "	int m = 2;"                                                          +"\n"+
		        		            ""                                                                     +"\n"+
		        		            "	sscanf (ptr1,\"%s %*s %d\", ptr2,&m); //DEFECT"                        +"\n"+
		        		            "}"                                                                    
		        		            ,
		        		            "gcc"
		        		            ,
		        		            "NPD_PRE"
		        		            ,
		        		            },
		        	/////////////////  54   ///////////////////	
		        		            {
		        		            "#include <string.h>"                                                  +"\n"+
		        		            ""                                                                     +"\n"+
		        		            "void func()"                                                          +"\n"+
		        		            "{"                                                                    +"\n"+
		        		            "	char *ptr1 = NULL;"                                                  +"\n"+
		        		            "	char *ptr2 = NULL;"                                                  +"\n"+
		        		            ""                                                                     +"\n"+
		        		            "	strcat(ptr1, ptr2); //DEFECT"                                        +"\n"+
		        		            "}"                                                                    
		        		            ,
		        		            "gcc"
		        		            ,
		        		            "NPD_PRE"
		        		            ,
		        		            },

        		        	/////////////////  55   ///////////////////	
        		        		            {
        		        		            "#include <string.h>"                                                  +"\n"+
        		        		            ""                                                                     +"\n"+
        		        		            "void func()"                                                          +"\n"+
        		        		            "{"                                                                    +"\n"+
        		        		            "	char *ptr1 = NULL;"                                                  +"\n"+
        		        		            "	char *ptr2 = NULL;"                                                  +"\n"+
        		        		            ""                                                                     +"\n"+
        		        		            "	strcmp(ptr1, ptr2); //DEFECT"                                        +"\n"+
        		        		            "}"                                                                    
        		        		            ,
        		        		            "gcc"
        		        		            ,
        		        		            "NPD_PRE"
        		        		            ,
        		        		            },
        		        	/////////////////  56   ///////////////////	
        		        		            {
        		        		            "#include <string.h>"                                                  +"\n"+
        		        		            ""                                                                     +"\n"+
        		        		            "void func()"                                                          +"\n"+
        		        		            "{"                                                                    +"\n"+
        		        		            "	char *ptr1 = NULL;"                                                  +"\n"+
        		        		            ""                                                                     +"\n"+
        		        		            "	strchr(ptr1, 's'); //DEFECT"                                         +"\n"+
        		        		            "}"                                                                    
        		        		            ,
        		        		            "gcc"
        		        		            ,
        		        		            "NPD_PRE"
        		        		            ,
        		        		            },

        		        		        	/////////////////  57   ///////////////////	
        		        		        		            {
        		        		        		            "#include <stdio.h>"                                                   +"\n"+
        		        		        		            ""                                                                     +"\n"+
        		        		        		            "void func()"                                                          +"\n"+
        		        		        		            "{"                                                                    +"\n"+
        		        		        		            "	char *ptr1 = NULL;"                                                  +"\n"+
        		        		        		            ""                                                                     +"\n"+
        		        		        		            "	puts(ptr1); //DEFECT"                                                +"\n"+
        		        		        		            "}"                                                                    
        		        		        		            ,
        		        		        		            "gcc"
        		        		        		            ,
        		        		        		            "NPD_PRE"
        		        		        		            ,
        		        		        		            },
        		        		        	/////////////////  58   ///////////////////	
        		        		        		            {
        		        		        		            "#include <stdlib.h>"                                                  +"\n"+
        		        		        		            ""                                                                     +"\n"+
        		        		        		            "void func()"                                                          +"\n"+
        		        		        		            "{"                                                                    +"\n"+
        		        		        		            "	qsort (NULL, 6, sizeof(int), NULL);//DEFECT"                         +"\n"+
        		        		        		            "}"                                                                    
        		        		        		            ,
        		        		        		            "gcc"
        		        		        		            ,
        		        		        		            "NPD_PRE"
        		        		        		            ,
        		        		        		            },
        		        		        		        	/////////////////  59   ///////////////////	
        		        		        		            {
        		        		        		            "#include <string.h>"                                                  +"\n"+
        		        		        		            ""                                                                     +"\n"+
        		        		        		            "void func()"                                                          +"\n"+
        		        		        		            "{"                                                                    +"\n"+
        		        		        		            "	char *ptr = NULL;"                                                   +"\n"+
        		        		        		            ""                                                                     +"\n"+
        		        		        		            "	memset(ptr,'*',6);//DEFECT"                                          +"\n"+
        		        		        		            "}"                                                                    
        		        		        		            ,
        		        		        		            "gcc"
        		        		        		            ,
        		        		        		            "NPD_PRE"
        		        		        		            ,
        		        		        		            },
        		        		        	/////////////////  60   ///////////////////	
        		        		        		            {
        		        		        		            "#include <string.h>"                                                  +"\n"+
        		        		        		            ""                                                                     +"\n"+
        		        		        		            "void func()"                                                          +"\n"+
        		        		        		            "{"                                                                    +"\n"+
        		        		        		            "	char *ptr1 = NULL;"                                                  +"\n"+
        		        		        		            "	char *ptr2 = NULL;"                                                  +"\n"+
        		        		        		            ""                                                                     +"\n"+
        		        		        		            "	memcpy(ptr1, ptr2, 6);//DEFECT"                                      +"\n"+
        		        		        		            "}"                                                                    
        		        		        		            ,
        		        		        		            "gcc"
        		        		        		            ,
        		        		        		            "NPD_PRE"
        		        		        		            ,
        		        		        		            },

        		        		        		        	/////////////////  61   ///////////////////	
        		        		        		        		            {
        		        		        		        		            "#include <math.h>"                                                    +"\n"+
        		        		        		        		            "#include <stdlib.h>"                                                  +"\n"+
        		        		        		        		            ""                                                                     +"\n"+
        		        		        		        		            "void func()"                                                          +"\n"+
        		        		        		        		            "{"                                                                    +"\n"+
        		        		        		        		            "	double a;"                                                           +"\n"+
        		        		        		        		            "	double *b=NULL;"                                                     +"\n"+
        		        		        		        		            "	double c=100000.567;"                                                +"\n"+
        		        		        		        		            ""                                                                     +"\n"+
        		        		        		        		            "	a = modf(c,b);//DEFECT"                                              +"\n"+
        		        		        		        		            "}"                                                                    
        		        		        		        		            ,
        		        		        		        		            "gcc"
        		        		        		        		            ,
        		        		        		        		            "NPD_PRE"
        		        		        		        		            ,
        		        		        		        		            },
        		        		        		        		        	///////////////// 62   ///////////////////	
        		        		        		        		            {
        		        		        		        		            "#include <string.h>"                                                  +"\n"+
        		        		        		        		            "#include <malloc.h>"                                                  +"\n"+
        		        		        		        		            "void jhb_npd_7_f1(){"                                                 +"\n"+
        		        		        		        		            "	char* p;"                                                            +"\n"+
        		        		        		        		            "	p=(char*)malloc(100);"                                               +"\n"+
        		        		        		        		            "	memset(p,0,100);      //DEFECT"                                      +"\n"+
        		        		        		        		            "}"                                                                    
        		        		        		        		            ,
        		        		        		        		            "gcc"
        		        		        		        		            ,
        		        		        		        		            "NPD_PRE"
        		        		        		        		            ,
        		        		        		        		            },
        		        		        		        	/////////////////  63   ///////////////////	
        		        		        		        		            {
        		        		        		        		            "#include <time.h>"                                                    +"\n"+
        		        		        		        		            "void jhb_npd_9_f1(){"                                                 +"\n"+
        		        		        		        		            "	struct tm * ptr;"                                                    +"\n"+
        		        		        		        		            "	ptr=(struct tm*)0;"                                                  +"\n"+
        		        		        		        		            "	asctime(ptr); //DEFECT"                                              +"\n"+
        		        		        		        		            "}"                                                                    
        		        		        		        		            ,
        		        		        		        		            "gcc"
        		        		        		        		            ,
        		        		        		        		            "NPD_PRE"
        		        		        		        		            ,
        		        		        		        		            },
        		        		        		        	/////////////////  64   ///////////////////	
        		        		        		        		            {
        		        		        		        		            "#include <stdlib.h>"                                                  +"\n"+
        		        		        		        		            "void jhb_npd_10_f1(char* str){"                                       +"\n"+
        		        		        		        		            "	float f;"                                                            +"\n"+
        		        		        		        		            "    f=atof(str);      //DEFECT"                                       +"\n"+
        		        		        		        		            "}"                                                                    +"\n"+
        		        		        		        		            "int jhb_npd_10_f2()"                                                  +"\n"+
        		        		        		        		            "{"                                                                    +"\n"+
        		        		        		        		            "	float t;"                                                            +"\n"+
        		        		        		        		            "	char *str=\"12345.67\";"                                               +"\n"+
        		        		        		        		            "	t=atof(str);       //FT"                                             +"\n"+
        		        		        		        		            "	return 0;"                                                           +"\n"+
        		        		        		        		            "}"                                                                    
        		        		        		        		            ,
        		        		        		        		            "gcc"
        		        		        		        		            ,
        		        		        		        		            "OK"
        		        		        		        		            ,
        		        		        		        		            },
        		        		        		        		        	/////////////////  65   ///////////////////	
        		        		        		        		            {
        		        		        		        		            "#include <stdlib.h>"                                                  +"\n"+
        		        		        		        		            "#include <stdio.h>"                                                   +"\n"+
        		        		        		        		            "void jhb_npd_11_f1(){"                                                +"\n"+
        		        		        		        		            "	char a[]=\"-100\";"                                                    +"\n"+
        		        		        		        		            "    char *b;"                                                         +"\n"+
        		        		        		        		            "	b=NULL;"                                                             +"\n"+
        		        		        		        		            "	int c;"                                                              +"\n"+
        		        		        		        		            "	c=atoi(a)+atoi(b);  //DEFECT"                                        +"\n"+
        		        		        		        		            "	printf(\"c=%d\\n\",c);"                                                 +"\n"+
        		        		        		        		            "}"                                                                    +"\n"+
        		        		        		        		            "void jhb_npd_11_f2()"                                                 +"\n"+
        		        		        		        		            "{"                                                                    +"\n"+
        		        		        		        		            "	char a[]=\"-100\";"                                                    +"\n"+
        		        		        		        		            "	char b[]=\"456\";"                                                     +"\n"+
        		        		        		        		            "	int c;"                                                              +"\n"+
        		        		        		        		            "	c=atoi(a)+atoi(b);  //FT"                                            +"\n"+
        		        		        		        		            "	printf(\"c=%d\\n\",c);"                                                 +"\n"+
        		        		        		        		            "}"                                                                    
        		        		        		        		            ,
        		        		        		        		            "gcc"
        		        		        		        		            ,
        		        		        		        		            "NPD_PRE"
        		        		        		        		            ,
        		        		        		        		            },
        		        		        		        	/////////////////  66   ///////////////////	
        		        		        		        		          //hcj函数返回值取不着
        		        		        		        		            {
        		        		        		        		            "#include <stdlib.h>"                                                  +"\n"+
        		        		        		        		            "#include <stdio.h>"                                                   +"\n"+
        		        		        		        		            "char* jhb_npd_12_f1(int t)"                                           +"\n"+
        		        		        		        		            "{"                                                                    +"\n"+
        		        		        		        		            "	if (t>0)"                                                            +"\n"+
        		        		        		        		            "	{"                                                                   +"\n"+
        		        		        		        		            "		char *c=\"234567890\";"                                               +"\n"+
        		        		        		        		            "		return c;"                                                          +"\n"+
        		        		        		        		            "	}"                                                                   +"\n"+
        		        		        		        		            "	return NULL;"                                                        +"\n"+
        		        		        		        		            "}"                                                                    +"\n"+
        		        		        		        		            "void jhb_npd_12_f2(int m){"                                           +"\n"+
        		        		        		        		            "	char a[]=\"1000000000\";"                                              +"\n"+
        		        		        		        		            "	char* b;"                                                            +"\n"+
        		        		        		        		            "	b=jhb_npd_12_f1(m);"                                                 +"\n"+
        		        		        		        		            "	long c;"                                                             +"\n"+
        		        		        		        		            "	c=atol(a)+atol(b);     //DEFECT"                                     +"\n"+
        		        		        		        		            "	printf(\"c=%d\\n\",c);"                                                 +"\n"+
        		        		        		        		            "}"                                                                    
        		        		        		        		            ,
        		        		        		        		            "gcc"
        		        		        		        		            ,
        		        		        		        		            "NPD_PRE"
        		        		        		        		            ,
        		        		        		        		            },
        		        		        		        		        	/////////////////  67   ///////////////////	
        		        		        		        		            {
        		        		        		        		            "#include <stdlib.h>"                                                  +"\n"+
        		        		        		        		            "#include <string.h>"                                                  +"\n"+
        		        		        		        		            "#include <stdio.h>"                                                   +"\n"+
        		        		        		        		            "int jhb_npd_14_f1(void)"                                              +"\n"+
        		        		        		        		            "{"                                                                    +"\n"+
        		        		        		        		            "	char *str = NULL;"                                                   +"\n"+
        		        		        		        		            "	str = (char*)calloc(10, sizeof(char));"                              +"\n"+
        		        		        		        		            "	strcpy(str, \"Hello\");         //DEFECT"                              +"\n"+
        		        		        		        		            "	printf(\"String is %s\\n\", str);"                                      +"\n"+
        		        		        		        		            "	free(str);"                                                          +"\n"+
        		        		        		        		            "	return 0;"                                                           +"\n"+
        		        		        		        		            "}"                                                                    
        		        		        		        		            ,
        		        		        		        		            "gcc"
        		        		        		        		            ,
        		        		        		        		            "NPD_PRE"
        		        		        		        		            ,
        		        		        		        		            },
        		        		        		        		        	/////////////////  68   ///////////////////	
        		        		        		        		            {
        		        		        		        		            "#include <string.h>"                                                  +"\n"+
        		        		        		        		            ""                                                                     +"\n"+
        		        		        		        		            "void zk_npd_1_f1(char *str1, char *str2)"                             +"\n"+
        		        		        		        		            "{"                                                                    +"\n"+
        		        		        		        		            "	strcoll(str1, str2); //DEFECT"                                       +"\n"+
        		        		        		        		            "	return;"                                                             +"\n"+
        		        		        		        		            "}"                                                                    +"\n"+
        		        		        		        		            ""                                                                     +"\n"+
        		        		        		        		            "void zk_npd_1_f2()"                                                   +"\n"+
        		        		        		        		            "{"                                                                    +"\n"+
        		        		        		        		            "	char *str1 = \"This is first\";"                                       +"\n"+
        		        		        		        		            "	char *str2 = \"Second\";"                                              +"\n"+
        		        		        		        		            ""                                                                     +"\n"+
        		        		        		        		            "	strcoll(str1, str2); //FP"                                           +"\n"+
        		        		        		        		            "}"                                                                    
        		        		        		        		            ,
        		        		        		        		            "gcc"
        		        		        		        		            ,
        		        		        		        		            "OK"
        		        		        		        		            ,
        		        		        		        		            },
        		        		        		        		        	/////////////////  69   ///////////////////	
        		        		        		        		            {
        		        		        		        		            "#include <stdio.h>"                                                   +"\n"+
        		        		        		        		            "int jhb_npd_26_f1(void)"                                              +"\n"+
        		        		        		        		            "{"                                                                    +"\n"+
        		        		        		        		            "	fputs(\"Hello world\\n\", NULL);"                                       +"\n"+
        		        		        		        		            "	return 0;"                                                           +"\n"+
        		        		        		        		            "}"                                                                    
        		        		        		        		            ,
        		        		        		        		            "gcc"
        		        		        		        		            ,
        		        		        		        		            "NPD_PRE"
        		        		        		        		            ,
        		        		        		        		            },
        		        		        		        	/////////////////  70   ///////////////////	
        		        		        		        		          //hcj函数返回值取不着
        		        		        		        		            {
        		        		        		        		            "#include <string.h>"                                                  +"\n"+
        		        		        		        		            "#include <stdio.h>"                                                   +"\n"+
        		        		        		        		            "int jhb_npd_28_f1(void)"                                              +"\n"+
        		        		        		        		            "{"                                                                    +"\n"+
        		        		        		        		            "	FILE *stream;"                                                       +"\n"+
        		        		        		        		            "	char msg[] = \"this is a test\";"                                      +"\n"+
        		        		        		        		            "	char buf[20];"                                                       +"\n"+
        		        		        		        		            "	stream = fopen(\"DUMMY.FIL\", \"w+\");"                                  +"\n"+
        		        		        		        		            "	fread(buf, strlen(msg)+1, 1,stream);  //DEFECT"                      +"\n"+
        		        		        		        		            "	printf(\"%s\\n\", buf);"                                                +"\n"+
        		        		        		        		            "	return 0;"                                                           +"\n"+
        		        		        		        		            "}"                                                                    
        		        		        		        		            ,
        		        		        		        		            "gcc"
        		        		        		        		            ,
        		        		        		        		            "NPD_PRE"
        		        		        		        		            ,
        		        		        		        		            },
        		        		        		        		        	/////////////////  71   ///////////////////	
        		        		        		        		            {
        		        		        		        		            "#include <stdio.h>"                                                   +"\n"+
        		        		        		        		            "int jhb_npd_15_f1(void)"                                              +"\n"+
        		        		        		        		            "{"                                                                    +"\n"+
        		        		        		        		            "	FILE *fp;"                                                           +"\n"+
        		        		        		        		            "	char ch;"                                                            +"\n"+
        		        		        		        		            "	fp = fopen(\"DUMMY.FIL\", \"w\");"                                       +"\n"+
        		        		        		        		            "	ch = fgetc(fp);"                                                     +"\n"+
        		        		        		        		            "	printf(\"%c\\n\",ch);"                                                  +"\n"+
        		        		        		        		            "	clearerr(fp);      //DEFECT"                                         +"\n"+
        		        		        		        		            "	fclose(fp);"                                                         +"\n"+
        		        		        		        		            "	return 0;"                                                           +"\n"+
        		        		        		        		            "}"                                                                    
        		        		        		        		            ,
        		        		        		        		            "gcc"
        		        		        		        		            ,
        		        		        		        		            "NPD_PRE"
        		        		        		        		            ,
        		        		        		        		            },
        		        		        		        	/////////////////  72   ///////////////////	
        		        		        		        		            {
        		        		        		        		            "#include <stdio.h>"                                                   +"\n"+
        		        		        		        		            "int jhb_npd_14_f1(void)"                                              +"\n"+
        		        		        		        		            "{"                                                                    +"\n"+
        		        		        		        		            "	FILE *stream;"                                                       +"\n"+
        		        		        		        		            "	stream = fopen(\"DUMMY.FIL\", \"r\");"                                   +"\n"+
        		        		        		        		            "	fgetc(stream);"                                                      +"\n"+
        		        		        		        		            "	if (feof(stream))     //DEFECT"                                      +"\n"+
        		        		        		        		            "		printf(\"We have reached end-of-file\\n\");"                           +"\n"+
        		        		        		        		            "	fclose(stream);"                                                     +"\n"+
        		        		        		        		            "	return 0;"                                                           +"\n"+
        		        		        		        		            "}"                                                                    
        		        		        		        		            ,
        		        		        		        		            "gcc"
        		        		        		        		            ,
        		        		        		        		            "NPD_PRE"
        		        		        		        		            ,
        		        		        		        		            },
        		        		        		        	/////////////////  73   ///////////////////	
        		        		        		        		          //hcj函数返回值取不着
        		        		        		        		            {
        		        		        		        		            "#include <stdio.h>"                                                   +"\n"+
        		        		        		        		            "int jhb_npd_18_f1(void){"                                             +"\n"+
        		        		        		        		            "	FILE *stream;"                                                       +"\n"+
        		        		        		        		            "	stream = fopen(\"DUMMY.FIL\", \"w\");"                                   +"\n"+
        		        		        		        		            "	if (ferror(stream))       //DEFECT"                                  +"\n"+
        		        		        		        		            "	{"                                                                   +"\n"+
        		        		        		        		            "		printf(\"Error reading from DUMMY.FIL\\n\");"                          +"\n"+
        		        		        		        		            "		clearerr(stream);"                                                +"\n"+
        		        		        		        		            "	}"                                                                   +"\n"+
        		        		        		        		            "	fclose(stream);"                                                   +"\n"+
        		        		        		        		            "	return 0;"                                                           +"\n"+
        		        		        		        		            "}"                                                                    
        		        		        		        		            ,
        		        		        		        		            "gcc"
        		        		        		        		            ,
        		        		        		        		            "NPD_PRE"
        		        		        		        		            ,
        		        		        		        		            },
        		        		        		        	/////////////////  74   ///////////////////	
        		        		        		        		            {
        		        		        		        		            "#include <string.h>"                                                  +"\n"+
        		        		        		        		            "#include <stdio.h>"                                                   +"\n"+
        		        		        		        		            "int jhb_npd_20_f1(void)"                                              +"\n"+
        		        		        		        		            "{"                                                                    +"\n"+
        		        		        		        		            "	FILE *stream;"                                                       +"\n"+
        		        		        		        		            "	char string[] = \"This is a test\";"                                   +"\n"+
        		        		        		        		            "	char ch;"                                                            +"\n"+
        		        		        		        		            "	stream = fopen(\"DUMMY.FIL\", \"w+\");"                                  +"\n"+
        		        		        		        		            "	ch = fgetc(stream);  //DEFECT"                                       +"\n"+
        		        		        		        		            "	return 0;"                                                           +"\n"+
        		        		        		        		            "}"                                                                    
        		        		        		        		            ,
        		        		        		        		            "gcc"
        		        		        		        		            ,
        		        		        		        		            "NPD_PRE"
        		        		        		        		            ,
        		        		        		        		            },
        		        		        		        	/////////////////  75   ///////////////////
        		        		        		        		            {
        		        		        		        		            "#include <string.h>"                                                  +"\n"+
        		        		        		        		            "#include <stdio.h>"                                                   +"\n"+
        		        		        		        		            "int jhb_npd_22_f1(void)"                                              +"\n"+
        		        		        		        		            "{"                                                                    +"\n"+
        		        		        		        		            "	FILE *stream;"                                                       +"\n"+
        		        		        		        		            "	char string[] = \"This is a test\";"                                   +"\n"+
        		        		        		        		            "	char msg[20];"                                                       +"\n"+
        		        		        		        		            "	stream = fopen(\"DUMMY.FIL\", \"w+\");"                                  +"\n"+
        		        		        		        		            "	fwrite(string, strlen(string), 1, stream);"                          +"\n"+
        		        		        		        		            "	fseek(stream, 0, SEEK_SET);"                                         +"\n"+
        		        		        		        		            "	fgets(msg, strlen(string)+1, stream);  //DEFECT"                     +"\n"+
        		        		        		        		            "	printf(\"%s\", msg);"                                                  +"\n"+
        		        		        		        		            "	fclose(stream);"                                                     +"\n"+
        		        		        		        		            "	return 0;"                                                           +"\n"+
        		        		        		        		            "} "                                                                   
        		        		        		        		            ,
        		        		        		        		            "gcc"
        		        		        		        		            ,
        		        		        		        		            "NPD_PRE"
        		        		        		        		            ,
        		        		        		        		            },
        		        		        		        	/////////////////  76   ///////////////////	
        		        		        		        		            {
        		        		        		        		            "#include <stdio.h>"                                                   +"\n"+
        		        		        		        		            "int jhb_npd_23_f1()"                                                  +"\n"+
        		        		        		        		            "{"                                                                    +"\n"+
        		        		        		        		            "	FILE *fp; "                                                          +"\n"+
        		        		        		        		            "	fp = fopen(\"myfile.ly\",\"w\"); "                                       +"\n"+
        		        		        		        		            "	fclose(fp);   //DEFECT"                                              +"\n"+
        		        		        		        		            "	return 0;"                                                           +"\n"+
        		        		        		        		            "}"                                                                    
        		        		        		        		            ,
        		        		        		        		            "gcc"
        		        		        		        		            ,
        		        		        		        		            "NPD_PRE"
        		        		        		        		            ,
        		        		        		        		            },
        		        		        		        	/////////////////  77   ///////////////////	
        		        		        		        		            {
        		        		        		        		            "#include <stdio.h> "                                                  +"\n"+
        		        		        		        		            "#include <process.h> "                                                +"\n"+
        		        		        		        		            " "                                                                    +"\n"+
        		        		        		        		            "void jhb_npd_24_f1( void ) "                                          +"\n"+
        		        		        		        		            "{ "                                                                   +"\n"+
        		        		        		        		            "	FILE *stream;"                                                       +"\n"+
        		        		        		        		            "	char s[] = \"this is a string\"; "                                     +"\n"+
        		        		        		        		            "	char c = '\\n'; "                                                     +"\n"+
        		        		        		        		            "	stream = fopen( \"fprintf.out\", \"w\" ); "                              +"\n"+
        		        		        		        		            "	fprintf( stream, \"%s%c\", s, c ); //DEFECT "                          +"\n"+
        		        		        		        		            "	system( \"type fprintf.out\" ); "                                      +"\n"+
        		        		        		        		            "} "                                                                   
        		        		        		        		            ,
        		        		        		        		            "gcc"
        		        		        		        		            ,
        		        		        		        		            "NPD_PRE"
        		        		        		        		            ,
        		        		        		        		            },
        		        		        		        	/////////////////  78   ///////////////////	
        		        		        		        		          //hcj函数返回值取不着
        		        		        		        		            {
        		        		        		        		            "#include<stdio.h>"                                                    +"\n"+
        		        		        		        		            "#include<stdlib.h>"                                                   +"\n"+
        		        		        		        		            "void jhb_npd_25_f1()"                                                 +"\n"+
        		        		        		        		            "{"                                                                    +"\n"+
        		        		        		        		            "	FILE *fpout;"                                                        +"\n"+
        		        		        		        		            "	char ch;"                                                            +"\n"+
        		        		        		        		            "	fpout=fopen(\"file_a.dat\",\"w\");"                                      +"\n"+
        		        		        		        		            "	ch=getchar();"                                                       +"\n"+
        		        		        		        		            "	for(;ch!='#';)"                                                      +"\n"+
        		        		        		        		            "	{"                                                                   +"\n"+
        		        		        		        		            "		fputc(ch,fpout);  //DEFECT"                                         +"\n"+
        		        		        		        		            "		ch=getchar();"                                                      +"\n"+
        		        		        		        		            "	}"                                                                   +"\n"+
        		        		        		        		            "	fclose(fpout);"                                                      +"\n"+
        		        		        		        		            "}"                                                                    
        		        		        		        		            ,
        		        		        		        		            "gcc"
        		        		        		        		            ,
        		        		        		        		            "NPD_PRE"
        		        		        		        		            ,
        		        		        		        		            },
        		        		        		        	/////////////////  79   ///////////////////	
        		        		        		        		            {
        		        		        		        		            "#include  <stdio.h>"                                                  +"\n"+
        		        		        		        		            "typedef  struct{"                                                     +"\n"+
        		        		        		        		            "    char a[22];"                                                      +"\n"+
        		        		        		        		            "    char* p;"                                                         +"\n"+
        		        		        		        		            "}S;"                                                                  +"\n"+
        		        		        		        		            "S  *s1,*s2;"                                                          +"\n"+
        		        		        		        		            "char *p;"                                                             +"\n"+
        		        		        		        		            "void f(){"                                                            +"\n"+
        		        		        		        		            "   *p='a';"                                                           +"\n"+
        		        		        		        		            "}"                                                                    +"\n"+
        		        		        		        		            "void f1(){"                                                           +"\n"+
        		        		        		        		            "   f();"                                                              +"\n"+
        		        		        		        		            "}"                                                                    +"\n"+
        		        		        		        		            "void f2(){"                                                           +"\n"+
        		        		        		        		            "   p=(char*)malloc(11);"                                              +"\n"+
        		        		        		        		            "   f1();"                                                             +"\n"+
        		        		        		        		            "}"                                                                    
        		        		        		        		            ,
        		        		        		        		            "gcc"
        		        		        		        		            ,
        		        		        		        		            "NPD_PRE"
        		        		        		        		            ,
        		        		        		        		            },
        		        		        		        	/////////////////  80   ///////////////////	
        		        		        		        		            {
        		        		        		        		            "#include  <stdio.h>"                                                  +"\n"+
        		        		        		        		            "typedef  struct{"                                                     +"\n"+
        		        		        		        		            "    char a[22];"                                                      +"\n"+
        		        		        		        		            "    char* p;"                                                         +"\n"+
        		        		        		        		            "}S;"                                                                  +"\n"+
        		        		        		        		            "S  *s1,*s2;"                                                          +"\n"+
        		        		        		        		            "char *p;"                                                             +"\n"+
        		        		        		        		            "void f(char* q){"                                                     +"\n"+
        		        		        		        		            "   *q='a';"                                                           +"\n"+
        		        		        		        		            "}"                                                                    +"\n"+
        		        		        		        		            "void f1(int i,char* q){"                                              +"\n"+
        		        		        		        		            "   f(q);"                                                             +"\n"+
        		        		        		        		            "}"                                                                    +"\n"+
        		        		        		        		            "void f2(){"                                                           +"\n"+
        		        		        		        		            "   p=(char*)malloc(11);"                                              +"\n"+
        		        		        		        		            "   f1(1,p);"                                                          +"\n"+
        		        		        		        		            "}"                                                                    
        		        		        		        		            ,
        		        		        		        		            "gcc"
        		        		        		        		            ,
        		        		        		        		            "NPD_PRE"
        		        		        		        		            ,
        		        		        		        		            },

        		        		        		        	///////////////// 81   ///////////////////	
        		        		        		        		            {
        		        		        		        		            "#include  <stdio.h>"                                                  +"\n"+
        		        		        		        		            "typedef  struct{"                                                     +"\n"+
        		        		        		        		            "    char a[22];"                                                      +"\n"+
        		        		        		        		            "    char* p;"                                                         +"\n"+
        		        		        		        		            "}S;"                                                                  +"\n"+
        		        		        		        		            "S  *s1,*s2;"                                                          +"\n"+
        		        		        		        		            ""                                                                     +"\n"+
        		        		        		        		            "void f(){"                                                            +"\n"+
        		        		        		        		            "   *(s1->p)='a';"                                                     +"\n"+
        		        		        		        		            "}"                                                                    +"\n"+
        		        		        		        		            "void f1(){"                                                           +"\n"+
        		        		        		        		            "   f();"                                                              +"\n"+
        		        		        		        		            "}"                                                                    +"\n"+
        		        		        		        		            "void f2(){"                                                           +"\n"+
        		        		        		        		            "   s1->p=(char*)malloc(11);"                                              +"\n"+
        		        		        		        		            "   f1();"                                                             +"\n"+
        		        		        		        		            "}"                                                                    
        		        		        		        		            ,
        		        		        		        		            "gcc"
        		        		        		        		            ,
        		        		        		        		            "NPD_PRE"
        		        		        		        		            ,
        		        		        		        		            },
        		        		        		        	///////////////// 82  ///////////////////	
        		        		        		        		            {
        		        		        		        		            "#include <stdio.h>"                                                   +"\n"+
        		        		        		        		            ""                                                                     +"\n"+
        		        		        		        		            "int* f(){"                                                            +"\n"+
        		        		        		        		            "   return (int*)malloc(11);"                                          +"\n"+
        		        		        		        		            "}"                                                                    +"\n"+
        		        		        		        		            "void f1(int *p){"                                                     +"\n"+
        		        		        		        		            "   *p;"                                                               +"\n"+
        		        		        		        		            "}"                                                                    +"\n"+
        		        		        		        		            "void f2(){"                                                           +"\n"+
        		        		        		        		            "   f1(f()); "                                                         +"\n"+
        		        		        		        		            "}"                                                                    
        		        		        		        		            ,
        		        		        		        		            "gcc"
        		        		        		        		            ,
        		        		        		        		            "NPD_PRE"
        		        		        		        		            ,
        		        		        		        		            },


 });
	 }
}
