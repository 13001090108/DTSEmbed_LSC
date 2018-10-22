package softtest.test.gcc.rules.fault;

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
public class Test_NPD_PRE extends ModelTestBase {
	public Test_NPD_PRE(String source,String compiletype, String result)
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
		Set<MethodNameDeclaration> libDecls = libManager.compileLib(pre.getLibIncludes());
		interContext = InterContext.getInstance();
		interContext.addLibMethodDecl(libDecls);
	}
	 @Parameters
	 public static Collection<Object[]> testcaseAndResults()
	 {
		 return Arrays.asList(new Object[][] {
///////////////////1///////////////////////////////////////////////
		            {
			            "#include <stdio.h>"                                                   +"\n"+
			            "#include <stdlib.h>"                                                  +"\n"+
			            ""                                                                     +"\n"+
			            "int main(int argc, char *argv[])"                                     +"\n"+
			            "{"                                                                    +"\n"+
			            "    char *p=(void*)0;"                                                         +"\n"+
			          
			            "   sscanf(\"123456 \", \"%s\", p);"                                       +"\n"+
			            "  return 0;"                                                          +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "NPD_PRE"
			            ,
			            },
	/////////////////  0  ///////////////////	
				 {    "#include <stdio.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            "#include <string.h>"                                                  +"\n"+

					"char *getString()"                                                    +"\n"+
					"{"                                                                    +"\n"+
					"    int a =0;"                                                        +"\n"+
					"    if(a)"                                                            +"\n"+
					"      return (char *)malloc(sizeof(char)*5);"                         +"\n"+
					"    else"                                                             +"\n"+
					"      return NULL;"                                                   +"\n"+
					"    }"                                                                +"\n"+
					"int main(int argc, char *argv[])"                                     +"\n"+
					"{"                                                                    +"\n"+
					"    "                                                                 +"\n"+
					"    char a[5];"                                                       +"\n"+
					"    //char *p = (char *)0;"                                           +"\n"+
					"    strcpy(a, getString());"                                          +"\n"+
					"    return 0;"                                                        +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"NPD_PRE"
,
},

		/////////////////  1   ///////////////////	
				    {
				    "#include<string.h>"                                                   +"\n"+
				    "#include<stdio.h>"                                                    +"\n"+
				    "#include<stdlib.h>"                                                   +"\n"+
				    "char* zquote_cmd_string(char *p,int k)"                               +"\n"+
				    "{"                                                                    +"\n"+
				    "   if(k<=0)"                                                          +"\n"+
				    "       return NULL;"                                                  +"\n"+
				    "   else"                                                              +"\n"+
				    "      {"                                                              +"\n"+
				    "          char * temp = (char *)malloc(k);"                           +"\n"+
				    "          strncpy(temp, k-1, p);"                                     +"\n"+
				    "          return temp;"                                               +"\n"+
				    "      } "                                                             +"\n"+
				    "}"                                                                    +"\n"+
				    "void test(char *z1,int k)"                                            +"\n"+
				    "{"                                                                    +"\n"+
				    "  if(*z1!='\\0')"                                                      +"\n"+
				    "  {"                                                                  +"\n"+
				    "     char *zq = zquote_cmd_string(z1,k);"                             +"\n"+
				    "     z1=zq;"                                                          +"\n"+
				    "     int len;"                                                        +"\n"+
				    "     len = strlen(z1);"                                               +"\n"+
				    "  }"                                                                  +"\n"+
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
		            "void npd_1_f2(char* q)"                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "	char a=*q;"                                                          +"\n"+
		            "}"                                                                    +"\n"+
		            "void npd_1_f3(int a)"                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *p=(void*)0;"                                            +"\n"+
		            "	npd_1_f2(p);  //defect"                                          +"\n"+
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
		            "char* npd_1_f1()"                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	return (void*)0;"                                                       +"\n"+
		            "}"                                                                    +"\n"+
		            "void npd_1_f2(char* q)"                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "	char a=*q;"                                                          +"\n"+
		            "}"                                                                    +"\n"+
		            "void npd_1_f3()"                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *p=npd_1_f1();"                                            +"\n"+
		            "	npd_1_f2(p);  //defect"                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	///////////////// 5   ///////////////////
		          //hcj函数返回值取不着
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "char* npd_1_f1(int b)"                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	char * p = NULL;"                                                       +"\n"+
		            "	return p;"                                                       +"\n"+
		            "}"                                                                    +"\n"+
		            "void npd_1_f2(char* q)"                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "	char a=*q;"                                                          +"\n"+
		            "}"                                                                    +"\n"+
		            "void npd_1_f3(int a)"                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *p=npd_1_f1(a);"                                            +"\n"+
		            "	npd_1_f2(p);  //defect"                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
	/////////////////  6  ///////////////////	
		            {
		            ""                                                                     +"\n"+
		            "int func5(int *a){"                                                   +"\n"+
		            "	*a = 1;  //FP,NPD"                                                   +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            "int main()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "	int a = 1;"                                                          +"\n"+
		            "	int* p;"                                                             +"\n"+
		            "	p = (void*)0;"                                                       +"\n"+
		            "	func5(p); //DEFECT,NPD,p"                                            +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	/////////////////  7   ///////////////////	
		            {
		            ""                                                                     +"\n"+
		            "int func5(int *a){"                                                   +"\n"+
		            "	*a = 1;  //FP,NPD"                                                   +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            "int main()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "	int a = 1;"                                                          +"\n"+
		            "	int* p;"                                                             +"\n"+
		            "	p = &a;"                                                             +"\n"+
		            "	func5(p);"                                                           +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  8 ///////////////////	
		            {
		            "int func7(int *a){"                                                   +"\n"+
		            "	if (a) {"                                                            +"\n"+
		            "		*a = 1; //FP,NPD"                                                   +"\n"+
		            "	}"                                                                   +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int func8(int *a){"                                                   +"\n"+
		            "	if (a != (void*)0) {"                                                +"\n"+
		            "		*a = 1;  //FP,NPD"                                                  +"\n"+
		            "	}"                                                                   +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int main()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "	int* p;"                                                             +"\n"+
		            "	p = (void*)0;"                                                       +"\n"+
		            "	func7(p); //FP,NPD"                                                  +"\n"+
		            "	func8(p); //FP,NPD"                                                  +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  9  ///////////////////	
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
		            ""                                                                     +"\n"
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },
		        	///////////////// 10   ///////////////////
		          //hcj函数返回值取不着
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "char* npd_1_f1(int b)"                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	if(b)"                                                               +"\n"+
		            "		return (void*)0;"                                                       +"\n"+
		            "	return (char*)malloc(10);"                                           +"\n"+
		            "}"                                                                    +"\n"+
		            "void npd_1_f2(char* q)"                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "	char a=*q;"                                                          +"\n"+
		            "}"                                                                    +"\n"+
		            "void npd_1_f3(int a)"                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *p=npd_1_f1(a);"                                            +"\n"+
		            "	npd_1_f2(p);  //defect"                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },	
		        	/////////////////  9   ///////////////////	
		            {
		            "#include <time.h>"                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func(const time_t * timer)"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	localtime(timer); //DEFECT"                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		            
////////////////	/  11   ///////////////////	
		            {
		            "int *p;"                                                              +"\n"+
		            "void f(int *p){"                                                      +"\n"+
		            "   *p;"                                                               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  12   ///////////////////	
		            {
		            "int *p;"                                                              +"\n"+
		            "int f()"                                                              +"\n"+
		            "{"                                                                    +"\n"+
		            "   *p;"                                                       +"\n"+
		            "}"                                                                    +"\n"+
		            "int g()"                                                              +"\n"+
		            "{"                                                                    +"\n"+
		            "   f();"                                                              +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  13   ///////////////////	
		            {
		            "char s[10];"                                                          +"\n"+
		            "void f()"                                                             +"\n"+
		            "{ "                                                                   +"\n"+
		            "  s[0] = 'a';"                                                        +"\n"+
		            "}"                                                                    +"\n"+
		            "void g()"                                                             +"\n"+
		            "{ "                                                                   +"\n"+
		            "   f();"                                                              +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  14   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            "#include <string.h>"                                                  +"\n"+
		            "#include <errno.h>"                                                   +"\n"+
		            "struct {"                                                             +"\n"+
		            "    char *name;"                                                      +"\n"+
		            "    int type;"                                                        +"\n"+
		            "} encode_tab[] = {"                                                   +"\n"+
		            "    {\"ean\",      2},"                                       +"\n"+
		            "    {\"ean13\",    2}"                                        +"\n"+
		            "};"                                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "int encode_id(char *encode_name)"                                     +"\n"+
		            "{"                                                                    +"\n"+
		            "    int i;"                                                           +"\n"+
		            "    for (i = 0;  encode_tab[i].name; i++)"                            +"\n"+
		            "	if (!strcasecmp(encode_tab[i].name, encode_name))"                   +"\n"+
		            "	    return encode_tab[i].type;"                                      +"\n"+
		            "    return -1;"                                                       +"\n"+
		            "}"                                                                    +"\n"+
		            "int get_encoding(void *arg)"                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "    encoding_type = encode_id((char *)arg); //FP"                          +"\n"+
		            "    if (encoding_type >=0) return 0;"                                 +"\n"+
		            "    fprintf(stderr, \"%s: wrong encoding \\\"%s\\\"\\n\", prgname,"          +"\n"+
		            "	    (char *)arg);"                                                   +"\n"+
		            "    return -2; /* error, no help */"                                  +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },

		 });
	 }
}
