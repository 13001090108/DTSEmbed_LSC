package softtest.test.c.gcc.regression_cpp;

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

					/////////////////  0 //////测试用例4_7本身又有错误   ///////////////////	
					{
						"typedef struct _SA {"                                                 +"\n"+
								"	int a;"                                                              +"\n"+
								"}SA;"                                                                 +"\n"+
								""                                                                     +"\n"+
								"int func_inter4_1(int re, int *a){"                                   +"\n"+
								"	*a = 1; //FP,NPD"                                                    +"\n"+
								"	return re;"                                                          +"\n"+
								"}"                                                                    +"\n"+
								""                                                                     +"\n"+
								"int func_inter4_2(int re, int *a){"                                   +"\n"+
								"	a[0] = 1; //FP,NPD"                                                  +"\n"+
								"	return re;"                                                          +"\n"+
								"}"                                                                    +"\n"+
								""                                                                     +"\n"+
								"int func_inter4_3(int re, SA* sa) {"                                  +"\n"+
								"	sa->a = 1; //FP,NPD"                                                 +"\n"+
								"	return re;"                                                          +"\n"+
								"}"                                                                    +"\n"+
								""                                                                     +"\n"+
								"int func_inter4_4(int re, int* b) {"                                  +"\n"+
								"	return func_inter4_1(re, b);"                                        +"\n"+
								"}"                                                                    +"\n"+
								""                                                                     +"\n"+
								"int func_inter4_5()"                                                  +"\n"+
								"{"                                                                    +"\n"+
								"	int a = 1;"                                                          +"\n"+
								"	int* p;"                                                             +"\n"+
								"	SA sa;"                                                              +"\n"+
								"	p = &a;"                                                             +"\n"+
								"	func_inter4_1(1, p);"                                                +"\n"+
								"	p = (void*)0;"                                                       +"\n"+
								"	func_inter4_1(1, p); //DEFECT,NPD,p"                                 +"\n"+
								"	return 0;"                                                           +"\n"+
								"}"                                                                    +"\n"+
								""                                                                     +"\n"+
								"int func_inter4_6()"                                                  +"\n"+
								"{"                                                                    +"\n"+
								"	int a = 1;"                                                          +"\n"+
								"	int* p;"                                                             +"\n"+
								"	SA sa;"                                                              +"\n"+
								"	p = &a;"                                                             +"\n"+
								"	func_inter4_2(1, p);"                                                +"\n"+
								"	p = (void*)0;"                                                       +"\n"+
								"	func_inter4_2(1, p); //DEFECT,NPD,p"                                 +"\n"+
								"	return 0;"                                                           +"\n"+
								"}"                                                                    +"\n"+
								""                                                                     +"\n"+
								""                                                                     +"\n"+
								"int func_inter4_7()"                                                  +"\n"+
								"{"                                                                    +"\n"+
								"	int a = 1;"                                                          +"\n"+
								"	SA* p;"                                                             +"\n"+
								"	SA sa;"                                                              +"\n"+
								"	p = &sa;"                                                             +"\n"+
								"	func_inter4_3(1, p);"                                                +"\n"+
								"	p = (void*)0;"                                                       +"\n"+
								"	func_inter4_3(1, p); //DEFECT,NPD,p"                                 +"\n"+
								"	return 0;"                                                           +"\n"+
								"}"                                                                    +"\n"+
								""                                                                     +"\n"+
								""                                                                     +"\n"+
								"int func_inter4_8()"                                                  +"\n"+
								"{"                                                                    +"\n"+
								"	int a = 1;"                                                          +"\n"+
								"	int* p;"                                                             +"\n"+
								"	SA sa;"                                                              +"\n"+
								"	p = &a;"                                                             +"\n"+
								"	func_inter4_4(1, p);"                                                +"\n"+
								"	p = (void*)0;"                                                       +"\n"+
								"	func_inter4_4(1, p); //DEFECT,NPD,p"                                 +"\n"+
								"	return 0;"                                                           +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},				
					///////////////// 1   ///////////////////	
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
					/////////////////  2   ///////////////////	
					{
						""                                                       +"\n"+
								"  	int* p;"                                                           +"\n"+
								"  	void f(){"                                                         +"\n"+
								"  		p=(void*)0;"                                                      +"\n"+
								"  		g();   //DEFECT,NPD,p"                                            +"\n"+
								"  	}"                                                                 +"\n"+
								""                                                                     +"\n"+
								"  	void g(){"                                                         +"\n"+
								"  		int i=*p;"                                                        +"\n"+
								"  	}"                                                                 +"\n"+
								""                                                                   
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  3   ///////////////////	
					{
						" //FP,NPD"                                              +"\n"+
								"  	int* p;"                                                           +"\n"+
								"  	void f1(){"                                                        +"\n"+
								"  		p=(void*)0;"                                                      +"\n"+
								"  		g1();"                                                            +"\n"+
								"  	}"                                                                 +"\n"+
								""                                                                     +"\n"+
								"		void f2(){"                                                         +"\n"+
								"  		p=(void*)0;"                                                      +"\n"+
								"  		g2();"                                                            +"\n"+
								"  	}"                                                                 +"\n"+
								"  	void g1(){"                                                        +"\n"+
								"  		if(p!=(void*)0){"                                                 +"\n"+
								"  			int i=*p;"                                                       +"\n"+
								"  		}"                                                                +"\n"+
								"  	}"                                                                 +"\n"+
								"  	"                                                                  +"\n"+
								"  	void g2() {"                                                       +"\n"+
								"  		if(p){"                                                           +"\n"+
								"  			int i=*p;"                                                       +"\n"+
								"  		}"                                                                +"\n"+
								"  	}"                                                                 +"\n"+
								" "                                                                  
								,
								"gcc"
								,
								"OK"
								,
					},
					/////////////////  4   ///////////////////	
					{
						"    "                                                   +"\n"+
								"  	int* p;"                                                           +"\n"+
								"  	void f(){"                                                         +"\n"+
								"  		h();"                                                             +"\n"+
								"  		g(); //DEFECT,NPD,p"                                              +"\n"+
								"  	}"                                                                 +"\n"+
								""                                                                     +"\n"+
								"  	void g(){"                                                         +"\n"+
								"  		int i=*p;"                                                        +"\n"+
								"  	}"                                                                 +"\n"+
								""                                                                     +"\n"+
								"  	void h(){"                                                         +"\n"+
								"  		p=(void*)0;"                                                      +"\n"+
								"  	}"                                                                 +"\n"+
								"  "                                                                 
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  5   ///////////////////	
					{
						        " "                                            +"\n"+
								"  	int* p;"                                                           +"\n"+
								"  	void f(){"                                                         +"\n"+
								"  		h();"                                                             +"\n"+
								"  		g();"                                                             +"\n"+
								"  	}"                                                                 +"\n"+
								"  	void g(){"                                                         +"\n"+
								"  		if(p!=(void*)0){"                                                 +"\n"+
								"  			int i=*p;"                                                       +"\n"+
								"  		}"                                                                +"\n"+
								"  	}"                                                                 +"\n"+
								"  	void h(){"                                                         +"\n"+
								"  		p=(void*)0;"                                                      +"\n"+
								"  	}"                                                                 +"\n"+
								"  "                                                                 
								,
								"gcc"
								,
								"OK"
								,
					},
					/////////////////  6   ///////////////////	
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
					/////////////////  7   ///////////////////	
					{
						        "   "                                                   +"\n"+
								"  	void f(int* p){"                                                   +"\n"+
								"  		g(p);"                                                            +"\n"+
								"  	}"                                                                 +"\n"+
								""                                                                     +"\n"+
								"  	void g(int* p){"                                                   +"\n"+
								"  		int i=*p;"                                                        +"\n"+
								"  	}"                                                                 +"\n"+
								"  	void h(){"                                                         +"\n"+
								"  		int* p=(void*)0;"                                                 +"\n"+
								"  		f(p); //DEFECT,NPD,p"                                             +"\n"+
								"  	}"                                                                 +"\n"+
								"  "                                                                 
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  8  ///////////////////	
					{
						        " "                                           +"\n"+
								"  	void f(int* p){"                                                   +"\n"+
								"  		if(p!=(void*)0)"                                                  +"\n"+
								"  			g(p);"                                                           +"\n"+
								"  	}"                                                                 +"\n"+
								""                                                                     +"\n"+
								"  	void g(int* p){"                                                   +"\n"+
								"  		int i=*p; //FP,NPD"                                               +"\n"+
								"  	}"                                                                 +"\n"+
								"  	void h(){"                                                         +"\n"+
								"  		int* p=(void*)0;"                                                 +"\n"+
								"  		f(p);"                                                            +"\n"+
								"  	}"                                                                 +"\n"+
								"  "                                                                 
								,
								"gcc"
								,
								"OK"
								,
					},
					/////////////////  9   ///////////////////	
					{
						"typedef struct _st {int a;} ST;"                                      +"\n"+
								"int* func1(int a){"                                                   +"\n"+
								"	return (void*)0;"                                                    +"\n"+
								"}"                                                                    +"\n"+
								""                                                                     +"\n"+
								"int func6(int* b) {"                                                  +"\n"+
								"	*b = 0;"                                                             +"\n"+
								"}"                                                                    +"\n"+
								""                                                                     +"\n"+
								"int main()"                                                           +"\n"+
								"{"                                                                    +"\n"+
								"	func6(func1(1)); //DEFECT,NPD,The 1 Param of function func6"         +"\n"+
								"	return 0;"                                                           +"\n"+
								"}"                                                                    +"\n"+
								""                                                                     +"\n"+
								"ST* func2() {"                                                        +"\n"+
								"	return (void*)0;"                                                    +"\n"+
								"}"                                                                    +"\n"+
								""                                                                     +"\n"+
								"void func3() {"                                                       +"\n"+
								"	int b = 0;"                                                          +"\n"+
								"	b = func2()->a; //FP,NPD"                                            +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					
					
					/////////////////  10   ///////////////////	
					{
						" "                                                     +"\n"+
								"  	void f(){"                                                         +"\n"+
								"  		g(h(1)); //DEFECT,NPD,The 1 Param of function g"                  +"\n"+
								"  	}"                                                                 +"\n"+
								""                                                                     +"\n"+
								"  	void g(int* p){"                                                   +"\n"+
								"  		int i=*p; "                                                       +"\n"+
								"  	}"                                                                 +"\n"+
								""                                                                     +"\n"+
								"  	int* h(int a){"                                                    +"\n"+
								"  		return (void*)0;"                                                 +"\n"+
								"  	}"                                                                 +"\n"+
								"  "                                                                 
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  11   ///////////////////	
					{
						"#include <string.h>"                                                  +"\n"+
								""                                                                     +"\n"+
								"int ghx_npd_26_f26 ()"                                                +"\n"+
								"{"                                                                    +"\n"+
								"  char *str = NULL;"                                                  +"\n"+
								"  char * pch;"                                                        +"\n"+
								"  int i=1;"                                                           +"\n"+
								"  pch=strchr(str,'s');//DEFECT"                                       +"\n"+
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
					/////////////////  13   ///////////////////	
					{
						" "                                                       +"\n"+
								"	void f(int* p){"                                                     +"\n"+
								"		g(p);"                                                              +"\n"+
								"	}"                                                                   +"\n"+
								""                                                                     +"\n"+
								"	void g(int* p){"                                                     +"\n"+
								"		if(p!=(void*)0)"                                                    +"\n"+
								"			int a=*p; //FP,NPD"                                                +"\n"+
								"	}"                                                                   +"\n"+
								"	void h(){"                                                           +"\n"+
								"		int* p=(void*)0;"                                                   +"\n"+
								"		f(p);"                                                              +"\n"+
								"	}"                                                                   +"\n"+
								""                                                                     +"\n"+
								""                                                                   
								,
								"gcc"
								,
								"OK"
								,
					},
					/////////////////  14   ///////////////////	
					{
						" "                                                       +"\n"+
								"	void f(int* p){"                                                     +"\n"+
								"		if(p!=(void*)0)"                                                    +"\n"+
								"			g(p);"                                                             +"\n"+
								"	}"                                                                   +"\n"+
								""                                                                     +"\n"+
								"	void g(int* p){"                                                     +"\n"+
								"		int a=*p;  //FP,NPD"                                                +"\n"+
								"	}"                                                                   +"\n"+
								"	void h(){"                                                           +"\n"+
								"		int* p=(void*)0;"                                                   +"\n"+
								"		f(p);"                                                              +"\n"+
								"	}"                                                                   +"\n"+
								""                                                                     +"\n"+
								""                                                                   
								,
								"gcc"
								,
								"OK"
								,
					},
					/////////////////  15   ///////////////////	
					{
						" "                                                       +"\n"+
								"	void f(int* p){"                                                     +"\n"+
								"		g(p);"                                                              +"\n"+
								"	}"                                                                   +"\n"+
								""                                                                     +"\n"+
								"	void g(int* p){"                                                     +"\n"+
								"		int a=*p;"                                                          +"\n"+
								"	}"                                                                   +"\n"+
								"	void h(int* p){"                                                     +"\n"+
								"		if(p==(void*)0){"                                                   +"\n"+
								"		}"                                                                  +"\n"+
								"		f(p);  //DEFECT,NPD,p"                                              +"\n"+
								"	}"                                                                   +"\n"+
								""                                                                     +"\n"+
								""                                                                   
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  16  ///////////////////	
					{
								"int func10_1(int *a){"                                                +"\n"+
								"	*a = 1;"                                                             +"\n"+
								"	return 0;"                                                           +"\n"+
								"}"                                                                    +"\n"+
								""                                                                     +"\n"+
								"int func10_2(int* b) {"                                               +"\n"+
								"	return func10_1(b);"                                                 +"\n"+
								"}"                                                                    +"\n"+
								""                                                                     +"\n"+
								"int func10_3()"                                                       +"\n"+
								"{"                                                                    +"\n"+
								"	int a = 1;"                                                          +"\n"+
								"	int* p;"                                                             +"\n"+
								"	p = &a;"                                                             +"\n"+
								"	func10_1(p);"                                                        +"\n"+
								"	p = (void*)0;"                                                       +"\n"+
								"	func10_1(p);  //DEFECT,NPD,p"                                        +"\n"+
								"	return 0;"                                                           +"\n"+
								"}"                                                                    +"\n"+
								""                                                                     +"\n"+
								"int func10_4()"                                                       +"\n"+
								"{"                                                                    +"\n"+
								"	int a = 1;"                                                          +"\n"+
								"	int* p;"                                                             +"\n"+
								"	p = &a;"                                                             +"\n"+
								"	func10_2(p);"                                                        +"\n"+
								"	p = (void*)0;"                                                       +"\n"+
								"	func10_2(p);  //DEFECT,NPD,p"                                        +"\n"+
								"	return 0;"                                                           +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  17   ///////////////////	
					{
						"#include <stdlib.h>"                                                  +"\n"+
								"char* f18_0(int flag){"                                               +"\n"+
								"	if(flag)"                                                            +"\n"+
								"		return NULL;"                                                       +"\n"+
								"	return (char*)malloc(10);"                                           +"\n"+
								"}"                                                                    +"\n"+
								"void f18_1(char* p){"                                                 +"\n"+
								"	char a=*p;"                                                          +"\n"+
								"}"                                                                    +"\n"+
								"void test18_2(int a)"                                                 +"\n"+
								"{"                                                                    +"\n"+
								"	char*p=f18_0(a);"                                                    +"\n"+
								"	f18_1(p);   //DEFECT,NPD,p"                                          +"\n"+
								"	free(p);"                                                            +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  18   ///////////////////	
					{
						"#include <stdlib.h>"                                                  +"\n"+
								"#include <unistd.h>"                                                  +"\n"+
								"#include <io.h>"                                                  +"\n"+
								"struct st{"                                                           +"\n"+
								"	char* str;"                                                          +"\n"+
								"};"                                                                   +"\n"+
								"void test18_1(int flag,char* to)"                                     +"\n"+
								"{"                                                                    +"\n"+
								"	struct st *s;"                                                       +"\n"+
								"	s=(struct st*)malloc(sizeof(struct st));"                                          +"\n"+
								"	read(1,s,sizeof(s));  //DEFECT,NPD,s "                               +"\n"+
								"	free(s);"                                                            +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  19   ///////////////////	
					{
						"#include <stdlib.h>"                                                  +"\n"+
								"#include <string.h>"                                                  +"\n"+
								""                                                                     +"\n"+
								"void ghx_npd_2_f2(int flag,char* to)"                                 +"\n"+
								"{"                                                                    +"\n"+
								"	char* from;"                                                         +"\n"+
								"    char* buffer =(char*) calloc(1, 10);"                             +"\n"+
								"	if(buffer){"                                                         +"\n"+
								"	}"                                                                   +"\n"+
								"    if (flag== 0) {"                                                  +"\n"+
								"		from = to;"                                                         +"\n"+
								"    }"                                                                +"\n"+
								"    else {"                                                           +"\n"+
								"        from = buffer;"                                               +"\n"+
								"    }"                                                                +"\n"+
								"    memcpy(from, to, 10);"                                            +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},								
					/////////////////  20   ///////////////////	
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
					/////////////////  21   ///////////////////	
					{
						"#include <time.h>"                                                    +"\n"+
								"#include <stdio.h>"                                                   +"\n"+
								"int ghx_npd_16_f16()"                                                 +"\n"+
								"{"                                                                    +"\n"+
								"struct tm * timeinfo=NULL;"                                           +"\n"+
								"mktime(timeinfo);//DEFECT"                                            +"\n"+
								"return 0;"                                                            +"\n"+
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
					///////////////// 23   ///////////////////	
					{
						"#include <string.h>"                                                  +"\n"+
								"#include <stdio.h>"                                                   +"\n"+
								"int ghx_npd_15_f15()"                                                 +"\n"+
								"{"                                                                    +"\n"+
								"char *str=NULL;"                                                      +"\n"+
								"memset(str,'*',6);//DEFECT"                                           +"\n"+
								"return 0;"                                                            +"\n"+
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
								"OK"
								,
					},
					/////////////////  25   ///////////////////	
					{
						"#include <stdio.h>"                                                   +"\n"+
								"#include <string.h>"                                                  +"\n"+
								""                                                                     +"\n"+
								"int ghx_npd_12_f12 (size_t len1,size_t len2)"                         +"\n"+
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
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  26   ///////////////////	
					{
						"#include <stdio.h>"                                                   +"\n"+
								"#include <string.h>"                                                  +"\n"+
								"int ghx_npd_12_f11 ()"                                                +"\n"+
								"{"                                                                    +"\n"+
								"  char str1[]=\"abcdefg\";"                                             +"\n"+
								"  char str2[]=\"abc\";"                                                 +"\n"+
								"  int n;"                                                             +"\n"+
								"  size_t len1, len2;"                                                 +"\n"+
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
								"OK"
								,
					},
					/////////////////  27   ///////////////////	
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
								"OK"
								,
					},
					/////////////////  29   ///////////////////	
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
					/////////////////  30   ///////////////////	
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
								"} "                                                                   
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  31   ///////////////////	
					{
						"#include <stdio.h>"                                                   +"\n"+
								"int ghx_npd_19_f19(void)"                                             +"\n"+
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
					/////////////////  32   ///////////////////	
					{
						"#include <time.h>"                                                    +"\n"+
								"#include <stdio.h>"                                                   +"\n"+
								"//#include <setjmp.h>"                                                  +"\n"+
								"#include <stdlib.h>"                                                  +"\n"+
								"#include <string.h>"                                                  +"\n"+
								"#include <math.h>"                                                    +"\n"+
								"int ghx_npd_8_f8 ()"                                                  +"\n"+
								"{"                                                                    +"\n"+
								"  FILE *fp;"                                                          +"\n"+
								"   int *e=NULL;"                                                      +"\n"+
								"   char *s=NULL;"                                                     +"\n"+
								"   char *str1=NULL;"                                                  +"\n"+
								"   char *str2=NULL;"                                                  +"\n"+
								"   char *str5=NULL;"                                                  +"\n"+
								"   char *ph;"                                                         +"\n"+
								"   int m, i=1,j=2;"                                                   +"\n"+
								"   double a;"                                                         +"\n"+
								"   double *b=NULL;"                                                   +"\n"+
								"   double c=100000.567;"                                              +"\n"+
								"  fp=fopen (\"myfile.txt\",\"w\");"                                       +"\n"+
								"  rewind (fp);//DEFECT"                                               +"\n"+
								"  setvbuf ( fp , NULL , _IOFBF , 1024 );//DEFECT"                     +"\n"+
								"  putc('S',fp);//DEFECT"                                              +"\n"+
								"  str1 = (char*) malloc (i+1);"                                       +"\n"+
								"	str1[i]='\\0';//DEFECT"                                               +"\n"+
								"  ph=(char *)memchr(str1,'p',10);//DEFECT"                            +"\n"+
								"    ph[i]=0;//DEFECT"                                                 +"\n"+
								"  sprintf (s, \"%d plus %d is %d\", i, j, i+j);//DEFECT"                +"\n"+
								"  mktime(NULL);//DEFECT"                                              +"\n"+
								"  localtime (NULL);//DEFECT"                                          +"\n"+
								"  //longjmp(e, 1);//DEFECT"                                             +"\n"+
								"  perror(str1);//DEFECT"                                              +"\n"+
								""                                                                     +"\n"+
								"  memcmp ( str1, str2, 1);//DEFECT"                                   +"\n"+
								"  memmove(str1,str2,10);//DEFECT"                                     +"\n"+
								"  remove(str1); //DEFECT"                                             +"\n"+
								"  rename( str1 , str2 );//DEFECT"                                     +"\n"+
								"  sscanf (str1,\"%s %*s %d\",str2,&m);//DEFECT"                         +"\n"+
								"  strcat (str1,str2);//DEFECT"                                        +"\n"+
								"  strcmp (str1,str2) ;//DEFECT"                                       +"\n"+
								"  strchr(str1,'s');//DEFECT"                                          +"\n"+
								""                                                                     +"\n"+
								"  puts(str5);//DEFECT"                                                +"\n"+
								"  qsort (NULL, 6, sizeof(int), NULL);//DEFECT"                        +"\n"+
								"  memset(str1,'*',6);//DEFECT"                                        +"\n"+
								"  memcpy(str1,str2,7);  //DEFECT"                                     +"\n"+
								"  a=modf(c,b);//DEFECT"                                               +"\n"+
								"  return 0;"                                                          +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  33   ///////////////////	
					{
						"#include <stdio.h>"                                                   +"\n"+
								""                                                                     +"\n"+
								"int ghx_npd_20_f20 ()"                                                +"\n"+
								"{"                                                                    +"\n"+
								"  FILE * pFile;"                                                      +"\n"+
								"  char c;"                                                            +"\n"+
								"  pFile=fopen(\"alphabet.txt\",\"wt\");"                                  +"\n"+
								"    for (c = 'A' ; c <= 'Z' ; c++)"                                   +"\n"+
								"    {"                                                                +"\n"+
								"    putc (c , pFile);//DEFECT"                                        +"\n"+
								"    }"                                                                +"\n"+
								"  fclose (pFile); //DEFECT"                                           +"\n"+
								"  return 0;"                                                          +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  34   ///////////////////	
					{
						"#include <stdio.h>"                                                   +"\n"+
								"int ghx_npd_20_f19()"                                                 +"\n"+
								"{"                                                                    +"\n"+
								"FILE * pFile;"                                                        +"\n"+
								"  char c;"                                                            +"\n"+
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
								"OK"
								,
					},
					/////////////////  35   ///////////////////	
					{
						"#include <stdio.h>"                                                   +"\n"+
								"#include <string.h>"                                                  +"\n"+
								""                                                                     +"\n"+
								"int ghx_npd_22_f22 ()"                                                +"\n"+
								"{"                                                                    +"\n"+
								"  char *str=NULL;"                                                    +"\n"+
								"  strcat (str,\"strings \");//DEFECT"                                   +"\n"+
								"  return 0;"                                                          +"\n"+
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
								"#include <string.h>"                                                  +"\n"+
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
								"OK"
								,
					},
					/////////////////  37   ///////////////////	
					{
						"#include <stdio.h>"                                                   +"\n"+
								""                                                                     +"\n"+
								"int ghx_npd_21_f21 ()"                                                +"\n"+
								"{"                                                                    +"\n"+
								"  char *string = NULL;"                                               +"\n"+
								"  puts (string);//DEFECT"                                             +"\n"+
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
								"int ghx_npd_21_f20()"                                                 +"\n"+
								"{"                                                                    +"\n"+
								"char *string=\"welcome to beijing\";"                                   +"\n"+
								"puts (string);//FP"                                                   +"\n"+
								"return 0;"                                                            +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"OK"
								,
					},
					/////////////////  39   ///////////////////	
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
					/////////////////  40   ///////////////////	
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
					/////////////////  41   ///////////////////	
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
					/////////////////  42   ///////////////////	
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
					/////////////////  43   ///////////////////	
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
					/////////////////  44   ///////////////////	
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
					/////////////////  45   ///////////////////	
					{
						"  void reassign(int *argument, int *p) {"                             +"\n"+
								"    if ((!argument)) return;"                                         +"\n"+
								"    *argument = *p;"                                                  +"\n"+
								"  }"                                                                  +"\n"+
								"  "                                                                   +"\n"+
								"  void npd_check_call_must(int *argument,int *p) {"                   +"\n"+
								"    if (p != 0) {"                                                    +"\n"+
								"      *p = 1;"                                                        +"\n"+
								"   }"                                                                 +"\n"+
								"   reassign(argument, p); //DEFECT"                                   +"\n"+
								" }"                                                                   
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  46   ///////////////////	
					{
						"#include <stdio.h>"                                                   +"\n"+
								"void func()"                                                          +"\n"+
								"{"                                                                    +"\n"+
								"	char *ptr = NULL;"                                                   +"\n"+
								"	perror(ptr); //DEFECT"                                               +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  47  ///////////////////	
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
					/////////////////  48   ///////////////////	
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
					/////////////////  49   ///////////////////	
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
					/////////////////  50   ///////////////////	
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
					/////////////////  51   ///////////////////	
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
					/////////////////  52   ///////////////////	
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
					/////////////////  53   ///////////////////	
					{
						"#include <time.h>"                                                    +"\n"+
								"int ghx_npd_8_f9 ()"                                                  +"\n"+
								"{"                                                                    +"\n"+
								"  time_t rawtime;"                                                    +"\n"+
								"  struct tm * timeinfo;"                                              +"\n"+
								""                                                                     +"\n"+
								"  time ( &rawtime );"                                                 +"\n"+
								"  timeinfo = localtime ( &rawtime ); //FP"                            +"\n"+
								"  return 0;"                                                          +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"OK"
								,
					},
					/////////////////  54   ///////////////////	
					{
						"#include <stdio.h>"                                                   +"\n"+
								"#include <setjmp.h>"                                                  +"\n"+
								""                                                                     +"\n"+
								"int ghx_npd_9_f9()"                                                   +"\n"+
								"{"                                                                    +"\n"+
								"  int *env=NULL;"                                                     +"\n"+
								"  int val=0;"                                                         +"\n"+
								"  "                                                                   +"\n"+
								"  if (!val) "                                                         +"\n"+
								"   longjmp(env, 1);//DEFECT"                                          +"\n"+
								"  return 0;"                                                          +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  55   ///////////////////	
					{
						"#include <stdio.h>"                                                   +"\n"+
								"#include <setjmp.h>"                                                  +"\n"+
								"int ghx_npd_9_f8()"                                                   +"\n"+
								"{"                                                                    +"\n"+
								"  jmp_buf env;"                                                       +"\n"+
								"  int val=0;"                                                         +"\n"+
								""                                                                     +"\n"+
								"  val=setjmp(env);"                                                   +"\n"+
								""                                                                     +"\n"+
								"  printf (\"val is %d\\n\",val);"                                        +"\n"+
								""                                                                     +"\n"+
								"  if (!val) longjmp(env, 1);//FP"                                     +"\n"+
								""                                                                     +"\n"+
								"  return 0;"                                                          +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"OK"
								,
					},

					/////////////////  56   ///////////////////	
					{
						"  void reassign(int *argument, int *p) {"                             +"\n"+
								"    if ((!argument)) return;"                                         +"\n"+
								"    *argument = *p;"                                                  +"\n"+
								"  }"                                                                  +"\n"+
								"  "                                                                   +"\n"+
								"  void npd_gen_call_must(int *argument) {"                            +"\n"+
								"    int *p = 0;"                                                      +"\n"+
								"    reassign(argument, p); //DEFECT"                                  +"\n"+
								"  }"                                                                  
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  57   ///////////////////	
					{
						"  void reassign(int *argument, int *p) {"                             +"\n"+
								"    if ((!argument)) return;"                                         +"\n"+
								"    *argument = *p;"                                                  +"\n"+
								"  }"                                                                  +"\n"+
								"  "                                                                   +"\n"+
								"  void npd_gen_call_might(int *argument, int *s) {"                   +"\n"+
								"    int *p = 0;"                                                      +"\n"+
								"    if (s) {"                                                         +"\n"+
								"      p = s;"                                                         +"\n"+
								"   }"                                                                 +"\n"+
								"   reassign(argument, p); //DEFECT"                                   +"\n"+
								" }"                                                                   
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  58   ///////////////////	
					{
						"#include <stdlib.h> "                                                 +"\n"+
								" void reassign(int *argument, int *p) {"                              +"\n"+
								"    if ((!argument)) return;"                                         +"\n"+
								"    *argument = *p;"                                                  +"\n"+
								"  }"                                                                  +"\n"+
								" "                                                                    +"\n"+
								"  int *mymalloc() {"                                                  +"\n"+
								"    int *res = (int *)malloc(sizeof(int));"                           +"\n"+
								"    if (!res) return 0;"                                              +"\n"+
								"    *res = 0;"                                                        +"\n"+
								"   return res;"                                                       +"\n"+
								" }"                                                                   +"\n"+
								" "                                                                    +"\n"+
								" void npd_func_call_might(int *argument, int* someCondition) {"       +"\n"+
								"   int *p = mymalloc();"                                              +"\n"+
								"   if (someCondition){"                                               +"\n"+
								"     p =someCondition;"                                               +"\n"+
								"   }"                                                                 +"\n"+
								"   reassign(argument, p); //DEFECT"                                   +"\n"+
								" }"                                                                   
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  59   ///////////////////	
					{
						"  void reassign(int *argument, int *p) {"                             +"\n"+
								"    if ((!argument)) return;"                                         +"\n"+
								"    *argument = *p;"                                                  +"\n"+
								"  }"                                                                  +"\n"+
								"  "                                                                   +"\n"+
								"  void npd_check_call_must(int *argument,int *p,int r) {"             +"\n"+
								"    if (p != 0) {"                                                    +"\n"+
								"      *p = 1;"                                                        +"\n"+
								"   }"                                                                 +"\n"+
								"    if(r)"                                                            +"\n"+
								"		reassign(argument, p); //DEFECT"                                    +"\n"+
								" }"                                                                   
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  60   ///////////////////	
					{
						"  void xstrcpy(char *dst, char *src) {"                               +"\n"+
								"    if (!src) return;"                                                +"\n"+
								"    dst[0] = src[0];"                                                 +"\n"+
								"  }"                                                                  +"\n"+
								"  "                                                                   +"\n"+
								"  char global_buf[256];"                                              +"\n"+
								"  "                                                                   +"\n"+
								"  void npd_gen_might(int flag, char *arg) {"                          +"\n"+
								"    char *p = global_buf;"                                            +"\n"+
								"   if (flag) p = 0;"                                                  +"\n"+
								"   if (arg) { p = arg; }"                                             +"\n"+
								"   xstrcpy(p, \"Hello\"); //DEFECT"                                     +"\n"+
								" }"                                                                   
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  61   ///////////////////	
					{
						"#include <stdlib.h>"                                                  +"\n"+
								"int* func2()"                                                         +"\n"+
								"{"                                                                    +"\n"+
								"		return NULL;"                                                       +"\n"+
								""                                                                     +"\n"+
								"}"                                                                    +"\n"+
								"int func3(int *ptr)"                                                  +"\n"+
								"{"                                                                    +"\n"+
								"	return *ptr;"                                                        +"\n"+
								"}"                                                                    +"\n"+
								""                                                                     +"\n"+
								"void func1()"                                                         +"\n"+
								"{"                                                                    +"\n"+
								"		func3(func2());  //FP"                                              +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  62   ///////////////////	
					{
						"#include <stdlib.h>"                                                  +"\n"+
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
					/////////////////  63   ///////////////////	
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
					/////////////////  64   ///////////////////	
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
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  65   ///////////////////	
					{
						"#include <stdlib.h>"                                                  +"\n"+
								"#include <stdio.h>"                                                   +"\n"+
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
								"OK"
								,
					},
					/////////////////  66   ///////////////////	
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
					///////////////// 67   ///////////////////	
					{
						"#include <time.h>"                                                    +"\n"+
								"int jhb_npd_16_f1( time_t* t)"                                        +"\n"+
								"{"                                                                    +"\n"+
								"	time(t);"                                                            +"\n"+
								"	return 0;"                                                           +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"OK"
								,
					},
					/////////////////  68   ///////////////////	
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
					{
						"#include <string.h>"                                                  +"\n"+
								"#include <stdio.h>"                                                   +"\n"+
								""                                                   +"\n"+
								"#include <io.h>"                                                      +"\n"+
								"void jhb_npd_19_f2(FILE *stream);"                                    +"\n"+
								"int jhb_npd_19_f1(void)"                                              +"\n"+
								"{"                                                                    +"\n"+
								"	FILE *stream;"                                                       +"\n"+
								"	char msg[] = \"This is a test\";"                                      +"\n"+
								"	stream = fopen(\"DUMMY.FIL\", \"w\");"                                   +"\n"+
								"	getch();"                                                            +"\n"+
								"	jhb_npd_19_f2(stream); //DEFECT"                                     +"\n"+
								"	getch();"                                                            +"\n"+
								"	return 0;"                                                           +"\n"+
								"}"                                                                    +"\n"+
								"void jhb_npd_19_f2(FILE *stream)"                                     +"\n"+
								"{"                                                                    +"\n"+
								"	int duphandle;"                                                      +"\n"+
								"	fflush(stream);       "                                              +"\n"+
								"	duphandle = dup(fileno(stream));"                                    +"\n"+
								"	close(duphandle);"                                          +"\n"+
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
					/////////////////  72   ///////////////////	
					{
						"#include <string.h>"                                                  +"\n"+
								"#include <stdio.h>"                                                   +"\n"+
								""                                                   +"\n"+
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
					
					/////////////////  73   ///////////////////	
					{
						"#include <string.h>"                                                  +"\n"+
								"#include <stdio.h>"                                                   +"\n"+
								"int jhb_npd_21_f1(void)"                                              +"\n"+
								"{"                                                                    +"\n"+
								"	FILE *stream;"                                                       +"\n"+
								"	char string[] = \"This is a test\";"                                   +"\n"+
								"	fpos_t filepos;"                                                     +"\n"+
								"	stream = fopen(\"DUMMY.FIL\", \"w+\");"                                  +"\n"+
								"	fwrite(string, strlen(string), 1, stream);"                          +"\n"+
								"	fgetpos(stream, &filepos);             //DEFECT"                     +"\n"+
								"	printf(\"The file pointer is at byte %ld\\n\", filepos);"               +"\n"+
								"	fclose(stream);"                                                     +"\n"+
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
					/////////////////  75   ///////////////////	
					{
						"#include <stdio.h>"                                                   +"\n"+
								"#include <stdlib.h>"                                                  +"\n"+
								"#include \"time.h\""                                                    +"\n"+
								"#include <math.h>"                                                    +"\n"+
								"int jhb_npd_29_f2(void){"                                             +"\n"+
								"	double mantissa, number;"                                            +"\n"+
								"	number = 8.0;"                                                       +"\n"+
								"	int i;"                                                              +"\n"+
								"	mantissa = frexp(number, NULL);   //DEFECT"                          +"\n"+
								"	fscanf(NULL,\"%d\",&i);             //DEFECT"                          +"\n"+
								"	return 0;"                                                           +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  76   ///////////////////	
					{
						"#include <stdio.h>"                                                   +"\n"+
								"#include <stdlib.h>"                                                  +"\n"+
								"#include \"time.h\""                                                    +"\n"+
								"#include <math.h>"                                                    +"\n"+
								"int jhb_npd_29_f3(void){"                                             +"\n"+
								"	FILE *stream;"                                                       +"\n"+
								"	fpos_t filepos;"                                                     +"\n"+
								"	stream = fopen(\"MYFILE.TXT\", \"w+\");"                                 +"\n"+
								"	fseek(stream, 0L, SEEK_END);      //DEFECT"                          +"\n"+
								"	fgetpos(stream, &filepos);        //DEFECT"                          +"\n"+
								"	ftell(stream);                    //DEFECT"                          +"\n"+
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
						"#include <stdio.h>"                                                   +"\n"+
								"#include <stdlib.h>"                                                  +"\n"+
								"#include \"time.h\""                                                    +"\n"+
								"#include <math.h>"                                                    +"\n"+
								"struct jhb_npd_29_s1"                                                 +"\n"+
								"{"                                                                    +"\n"+
								"	int i;"                                                              +"\n"+
								"	char ch;"                                                            +"\n"+
								"};"                                                                   +"\n"+
								"int jhb_npd_29_f4(void)"                                              +"\n"+
								"{"                                                                    +"\n"+
								"	FILE *stream;"                                                       +"\n"+
								"	struct jhb_npd_29_s1 s;"                                             +"\n"+
								"	s.i = 0;"                                                            +"\n"+
								"	s.ch = 'A';"                                                         +"\n"+
								"	char ch;"                                                            +"\n"+
								"	char* p;"                                                            +"\n"+
								"	stream = fopen(\"TEST.$$$\", \"wb\");"                                   +"\n"+
								"	fwrite(&s, sizeof(s), 1, stream); //DEFECT"                          +"\n"+
								"	ch=getc(stream);                  //DEFECT"                          +"\n"+
								"	p=getenv(NULL);                   //DEFECT"                          +"\n"+
								"	p=gets(NULL);                     //DEFECT"                          +"\n"+
								"	gmtime(NULL);                     //DEFECT"                          +"\n"+
								"	return 0;"                                                           +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  78   ///////////////////	
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
					
					
					/////////////////  79   ///////////////////	
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
					/////////////////  80  ///////////////////	
					{
						"#include <string.h>"                                                  +"\n"+
								"#include <stdio.h>"                                                   +"\n"+
								""                                                                     +"\n"+
								"void zk_npd_10_f1()"                                                  +"\n"+
								"{"                                                                    +"\n"+
								"	char *str = NULL;"                                                   +"\n"+
								"	char *pch;"                                                          +"\n"+
								"	pch = strrchr(str, 's'); //DEFECT"                                   +"\n"+
								"	printf(\"%c\", *pch); //DEFECT"                                        +"\n"+
								"	return;"                                                             +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  81  ///////////////////	
					{
						"#include <string.h>"                                                  +"\n"+
								"#include <stdio.h>"                                                   +"\n"+
								"void zk_npd_10_f2()"                                                  +"\n"+
								"{"                                                                    +"\n"+
								"	char str[] = \"This is a sample\";"                                    +"\n"+
								"	char *pch;"                                                          +"\n"+
								"	pch = strrchr(str, 's'); //FP"                                       +"\n"+
								"	if (pch)"                                                            +"\n"+
								"		printf(\"%c\", *pch); //FP"                                           +"\n"+
								"	return;"                                                             +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"OK"
								,
					},
					/////////////////  82   ///////////////////	
					{
						"#include <stdlib.h>"                                                  +"\n"+
								""                                                                     +"\n"+
								"void zk_npd_15_f1()"                                                  +"\n"+
								"{"                                                                    +"\n"+
								"	char *str = NULL;"                                                   +"\n"+
								""                                                                     +"\n"+
								"	strtoul(str, NULL, 2); //DEFECT"                                     +"\n"+
								"	return;"                                                             +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},

					/////////////////  83   ///////////////////	
					{
						"#include <string.h>"                                                  +"\n"+
								""                                                                     +"\n"+
								"char *zk_npd_11_g1 = NULL;"                                           +"\n"+
								"char *zk_npd_11_g2 = NULL;"                                           +"\n"+
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
					/////////////////  84   ///////////////////	
					{
						"#include <string.h>"                                                  +"\n"+
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
					/////////////////  85  ///////////////////	
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
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  86  ///////////////////	
					{
						"#include <stdlib.h>"                                                  +"\n"+
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
								"OK"
								,
					},
					/////////////////  87   ///////////////////	
					{
						"#include <stdlib.h>"                                                  +"\n"+
								""                                                                     +"\n"+
								"void zk_npd_15_f1()"                                                  +"\n"+
								"{"                                                                    +"\n"+
								"	char *str = NULL;"                                                   +"\n"+
								""                                                                     +"\n"+
								"	strtol(str, NULL, 2); //DEFECT"                                      +"\n"+
								"	return;"                                                             +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  88   ///////////////////	
					{
						"#include <stdlib.h>"                                                  +"\n"+
								""                                                                     +"\n"+
								"void zk_npd_13_f1()"                                                  +"\n"+
								"{"                                                                    +"\n"+
								"	char *str = NULL;"                                                   +"\n"+
								""                                                                     +"\n"+
								"	strtod(str, NULL); //DEFECT"                                         +"\n"+
								"	return;"                                                             +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  89   ///////////////////	
					{
						"#include <string.h>"                                                  +"\n"+
								"#include <stdlib.h>"                                                  +"\n"+
								""                                                                     +"\n"+
								"#define MAXSIZE 1024"                                                 +"\n"+
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
								"OK"
								,
					},
					/////////////////  90   ///////////////////	
					{
						"#include <string.h>"                                                  +"\n"+
								"#include <stdio.h>"                                                   +"\n"+
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
					/////////////////  91   ///////////////////	
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
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  92   ///////////////////	
					{
						"#include <stdio.h>"                                                   +"\n"+
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
								"OK"
								,
					},
					/////////////////  93   ///////////////////	
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
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  94   ///////////////////	
					{
						"#include <string.h>"                                                  +"\n"+
								"void zk_npd_17_f2()"                                                  +"\n"+
								"{"                                                                    +"\n"+
								"	char des[10];"                                                       +"\n"+
								"	char src[] = \"sample\";"                                              +"\n"+
								"	strxfrm(des, src, sizeof(src)); //FP"                                +"\n"+
								"	return;"                                                             +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"OK"
								,
					},
					/////////////////  95   ///////////////////	
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
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  96   ///////////////////	
					{
						"#include <stdio.h>"                                                   +"\n"+
								"#include <stdarg.h>"                                                  +"\n"+
								""                                                                     +"\n"+
								"void zk_npd_24_f1(char *format, ...)"                                 +"\n"+
								"{"                                                                    +"\n"+
								"	char *buf = NULL;"                                                   +"\n"+
								"	va_list args;"                                                       +"\n"+
								""                                                                     +"\n"+
								"	va_start(args, format);"                                             +"\n"+
								"	vsprintf(buf, format, args); //DEFECT"                               +"\n"+
								"	va_end(args);"                                                       +"\n"+
								"	return;"                                                             +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  97   ///////////////////	
					{
						"#include <stdio.h>"                                                   +"\n"+
								"#include <stdarg.h>"                                                  +"\n"+
								""                                                                     +"\n"+
								"void zk_npd_22_f1(FILE *fp, char *format, ...)"                       +"\n"+
								"{"                                                                    +"\n"+
								"	va_list args;"                                                       +"\n"+
								"	va_start(args, format);"                                             +"\n"+
								"	vfprintf(fp, format, args); //DEFECT"                                +"\n"+
								"	va_end(args);"                                                       +"\n"+
								"	return;"                                                             +"\n"+
								"}"                                                                    +"\n"+
								""                                                                     +"\n"+
								"void zk_npd_22_f2()"                                                  +"\n"+
								"{"                                                                    +"\n"+
								"	FILE *stream = NULL;"                                                +"\n"+
								""                                                                     +"\n"+
								"	zk_npd_22_f1(stream, NULL, NULL);"                                   +"\n"+
								"	return;"                                                             +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  98   ///////////////////	
					{
						"#include <stdio.h>"                                                   +"\n"+
								"#include <stdarg.h>"                                                  +"\n"+
								"void zk_npd_22_f3(FILE *fp, char *format, ...)"                       +"\n"+
								"{"                                                                    +"\n"+
								"	char *ptr;"                                                          +"\n"+
								"	if (fp == NULL || format == NULL)"                                   +"\n"+
								"		return;"                                                            +"\n"+
								"	va_list args;"                                                       +"\n"+
								"	va_start(args, format);"                                             +"\n"+
								"	ptr = va_arg(args, char *);"                                         +"\n"+
								"	if (ptr == NULL) {"                                                  +"\n"+
								"		va_end(args);"                                                      +"\n"+
								"		return;"                                                            +"\n"+
								"	}"                                                                   +"\n"+
								"	vfprintf(fp, format, args); //FP"                                    +"\n"+
								"	va_end(args);"                                                       +"\n"+
								"	return;"                                                             +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"OK"
								,
					},
					/////////////////  99   ///////////////////	
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
					/////////////////  100   ///////////////////	
					{
						"#include <stdio.h>"                                                   +"\n"+
								"#include <stdarg.h>"                                                  +"\n"+
								"void zk_npd_24_f2(char *buf, char *format, ...)"                      +"\n"+
								"{"                                                                    +"\n"+
								"	char *ptr;"                                                          +"\n"+
								"	va_list args;"                                                       +"\n"+
								""                                                                     +"\n"+
								"	if (buf == NULL || format == NULL)"                                  +"\n"+
								"		return;"                                                            +"\n"+
								"	va_start(args, format);"                                             +"\n"+
								"	ptr = va_arg(args, char *);"                                         +"\n"+
								"	if (ptr == NULL) {"                                                  +"\n"+
								"		va_end(args);"                                                      +"\n"+
								"		return;"                                                            +"\n"+
								"	}"                                                                   +"\n"+
								"	vsprintf(buf, format, args); //FP"                                   +"\n"+
								"	va_end(args);"                                                       +"\n"+
								"	return;"                                                             +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"OK"
								,
					},
					/////////////////  101   ///////////////////	
					{
						"#include <stdio.h>"                                                   +"\n"+
								"#include <stdarg.h>"                                                  +"\n"+
								""                                                                     +"\n"+
								"void zk_npd_23_f1(char *format, ...)"                                 +"\n"+
								"{"                                                                    +"\n"+
								"	va_list args;"                                                       +"\n"+
								"	va_start(args, format);"                                             +"\n"+
								"	vprintf(format, args); //DEFECT"                                     +"\n"+
								"	va_end(args);"                                                       +"\n"+
								"	return;"                                                             +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"OK"
								,
					},
					/////////////////  102   ///////////////////	
					{
						"#include <stdio.h>"                                                   +"\n"+
								"#include <stdarg.h>"                                                  +"\n"+
								"void zk_npd_23_f2(char *format, ...)"                                 +"\n"+
								"{"                                                                    +"\n"+
								"	char *ptr;"                                                          +"\n"+
								"	if (format == NULL)"                                                 +"\n"+
								"		return;"                                                            +"\n"+
								"	va_list args;"                                                       +"\n"+
								"	va_start(args, format);"                                             +"\n"+
								"	ptr = va_arg(args, char *);"                                         +"\n"+
								"	if (ptr = NULL) {"                                                   +"\n"+
								"		va_end(args);"                                                      +"\n"+
								"		return;"                                                            +"\n"+
								"	}"                                                                   +"\n"+
								"	vprintf(format, args); //FP"                                         +"\n"+
								"	va_end(args);"                                                       +"\n"+
								"	return;"                                                             +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"OK"
								,
					},
					/////////////////  103   ///////////////////	
					{
						"#include <stdlib.h>"                                                  +"\n"+
								""                                                                     +"\n"+
								"void zk_npd_26_f1(wchar_t wc)"                                        +"\n"+
								"{"                                                                    +"\n"+
								"	wctomb(NULL, wc); //DEFECT"                                          +"\n"+
								"	return;"                                                             +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  104   ///////////////////	
					{
						"#include <stdlib.h>"                                                  +"\n"+
								"void zk_npd_26_f2(char *mb, wchar_t wc)"                              +"\n"+
								"{"                                                                    +"\n"+
								"	if (mb == NULL)"                                                     +"\n"+
								"		return;"                                                            +"\n"+
								"	wctomb(mb, wc); //FP"                                                +"\n"+
								"	return;"                                                             +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"OK"
								,
					},
					/////////////////  105   ///////////////////	
					{
						"#include <stdlib.h>"                                                  +"\n"+
								""                                                                     +"\n"+
								"void zk_npd_25_f1()"                                                  +"\n"+
								"{"                                                                    +"\n"+
								"	wcstombs(NULL, NULL, 0); //DEFECT"                                   +"\n"+
								"	return;"                                                             +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  106   ///////////////////	
					{
						"#include <string.h>"                                                  +"\n"+
								""                                                                     +"\n"+
								"void zk_npd_3_f1()"                                                   +"\n"+
								"{"                                                                    +"\n"+
								"	char *str1 = NULL;"                                                  +"\n"+
								"	char *str2 = NULL;"                                                  +"\n"+
								"	strcspn(str1, str2); //DEFECT"                                       +"\n"+
								"	return;"                                                             +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  107   ///////////////////	
					{
						"#include <string.h>"                                                  +"\n"+
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
								"OK"
								,
					},
					/////////////////  108   ///////////////////	
					{
						"#include <stdlib.h>"                                                  +"\n"+
								"void zk_npd_25_f2(char *mbstr, wchar_t *wcstr)"                       +"\n"+
								"{"                                                                    +"\n"+
								"	if (mbstr == NULL || wcstr == NULL)"                                 +"\n"+
								"		return;"                                                            +"\n"+
								"	wcstombs(mbstr, wcstr, sizeof(mbstr)); //FP"                         +"\n"+
								"	return;"                                                             +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"OK"
								,
					},
					////////////////////////////  109   ///////////////////	
					//在检查全局变量zk_npd_11_g1，zk_npd_11_g2区间的时候出现的问题
					//           -------聂敏慧
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
								"}"                                                                    
								,
								"gcc"
								,
								"OK"
								,
					},
					//////////////////////////  110  ///////////////////	
					{
						"#include <stdio.h>"                                                   +"\n"+
								""                                                                     +"\n"+
								"#define SIZE 5"                                                       +"\n"+
								""                                                                     +"\n"+
								"int zk_npd_43_g1[SIZE] = {1,2,3,4,5};"                                +"\n"+
								"int *zk_npd_43_g2 = NULL;"                                            +"\n"+
								""                                                                     +"\n"+
								"void main()"                                                          +"\n"+
								"{"                                                                    +"\n"+
								"	int i;"                                                              +"\n"+
								"	zk_npd_43_g2 = zk_npd_43_g1;"                                        +"\n"+
								""                                                                     +"\n"+
								"	for (i = 0; i < SIZE; i++) {"                                        +"\n"+
								"		printf(\"%d \", zk_npd_43_g2[i]); //FP"                               +"\n"+
								"	}"                                                                   +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"OK"
								,
					},
					/////////////////////////// 111   ///////////////////
					{
						"#include <stdio.h>"                                                   +"\n"+
								""                                                                     +"\n"+
								"int *tmp;"                                                            +"\n"+
								"int *ptr = NULL;"                                                     +"\n"+
								"int buf[10];"                                                         +"\n"+
								""                                                                     +"\n"+
								"void func3()"                                                         +"\n"+
								"{"                                                                    +"\n"+
								"	*tmp = 3;"                                                           +"\n"+
								"}"                                                                    +"\n"+
								""                                                                     +"\n"+
								"void func2()"                                                         +"\n"+
								"{"                                                                    +"\n"+
								"	tmp = ptr;"                                                          +"\n"+
								"	func3(); //FP"                                                       +"\n"+
								"}"                                                                    +"\n"+
								""                                                                     +"\n"+
								"void func1()"                                                         +"\n"+
								"{"                                                                    +"\n"+
								"	ptr = buf;"                                                          +"\n"+
								"	func2();"                                                            +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"OK"
								,
					},
					/////////////////  112   ///////////////////	
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
				
					///////////////113/////////////////	
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
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					///////////////////////////  114   ///////////////////	
					//strtok函数特殊
					{
						"#include <string.h>"                                                  +"\n"+
								""                                                                     +"\n"+
								"void zk_npd_45_f1(char *tmp)"                                         +"\n"+
								"{"                                                                    +"\n"+
								"	char *token;"                                                        +"\n"+
								"	char sep[] = \"\\n\";"                                                  +"\n"+
								""                                                                     +"\n"+
								"	token = strtok(tmp, sep);"                                           +"\n"+
								"	token = strtok(NULL, sep); //FP"                                     +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////  115   ///////////////////	
					{
						"#include <stdio.h>"                                                   +"\n"+
								"#include <stdlib.h>"                                                  +"\n"+
								""                                                                     +"\n"+
								"void zk_npd_35_f1()"                                                  +"\n"+
								"{"                                                                    +"\n"+
								"	char *key;"                                                          +"\n"+
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
					//////////////////////////  116   ///////////////////	
					//在库函数的NPD摘要中，要求检查函数strtod的两个参数，要求都为非空，所以这个用例的结果不应该是OK，应该为NPD吧
					//           -------聂敏慧
					{
						"#include <stdlib.h>"                                                  +"\n"+
								"void zk_npd_13_f2()"                                                  +"\n"+
								"{"                                                                    +"\n"+
								"	char str[] = \"3.14159\";"                                             +"\n"+
								""                                                                     +"\n"+
								"	strtod(str, NULL);"                                             +"\n"+
								"	return;"                                                             +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					//////////////////////////  117   ////////////////////////
					//这个用例应该是OK吧，time参数可以为空,当time参数为空（NULL），函数将只通过返回值返回现在的日历时间
					//           -------聂敏慧
					{
						"#include <time.h>"                                                    +"\n"+
								""                                                                     +"\n"+
								"void zk_npd_20_f1()"                                                  +"\n"+
								"{"                                                                    +"\n"+
								"	time_t seconds;"                                                     +"\n"+
								""                                                                     +"\n"+
								"	seconds = time(NULL); //FP"                                          +"\n"+
								"	return;"                                                             +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"OK"
								,
					},
					/////////////////  118   ///////////////////	
					{
						"#include <time.h>"                                                    +"\n"+
								""                                                                     +"\n"+
								"#define MAXSIZE 1024"                                                 +"\n"+
								""                                                                     +"\n"+
								"void zk_npd_4_f1()"                                                   +"\n"+
								"{"                                                                    +"\n"+
								"	char *ptr = NULL;"                                                   +"\n"+
								"	char *format = NULL;"                                                +"\n"+
								"	struct tm *timeptr = NULL;"                                          +"\n"+
								""                                                                     +"\n"+
								"	strftime(ptr, MAXSIZE, format, timeptr); //DEFECT"                   +"\n"+
								"	return;"                                                             +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					///////////////119/////////////////	
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
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},				
					/////////////////  120   ///////////////////	
					{
						"#include <time.h>"                                                    +"\n"+
								""                                                                     +"\n"+
								"#define MAXSIZE 1024"                                                 +"\n"+
								"void zk_npd_4_f2()"                                                   +"\n"+
								"{"                                                                    +"\n"+
								"	char ptr[MAXSIZE];"                                                  +"\n"+
								"	time_t rawtime;"                                                     +"\n"+
								"	struct tm *timeptr;"                                                 +"\n"+
								""                                                                     +"\n"+
								"	time(&rawtime);"                                                     +"\n"+
								"	timeptr = localtime(&rawtime);"                                      +"\n"+
								""                                                                     +"\n"+
								"	strftime(ptr, MAXSIZE, \"Time is %c\", timeptr); //FP"                 +"\n"+
								"	return;"                                                             +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"OK"
								,
					},
					
					/////////////////  121   ///////////////////	
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
					/////////////////  122   ///////////////////	
					{
						"#include <string.h>"                                                  +"\n"+
								"#include <stdio.h>"                                                   +"\n"+
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
								"OK"
								,
					}, 

					/////////////////  123  ///////////////////	
					{
						"//#include <stdlib.h>"                                                  +"\n"+
								"#include <string.h>"                                                  +"\n"+
								"void test18_4(int flag,char* to)"                                     +"\n"+
								"{"                                                                    +"\n"+
								"	char* from;"                                                         +"\n"+
								"    char* buffer =(char*) malloc(1);"                                 +"\n"+
								"	if(buffer){"                                                         +"\n"+
								"	}"                                                                   +"\n"+
								"    if (flag== 0) {"                                                  +"\n"+
								"		from=to;"                                                           +"\n"+
								"    }"                                                                +"\n"+
								"    else {"                                                           +"\n"+
								"        from = buffer;"                                               +"\n"+
								"    }"                                                                +"\n"+
								"    memcpy(from, to, 10); //DEFECT,NPD, from"                         +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					/////////////////////////  124///////////////////	
					{
						"#include<string.h>"                                                   +"\n"+
								"void feat_s2mfc2feat(const char *cepext)"                             +"\n"+
								"{"                                                                    +"\n"+
								"    if (cepext == 0)"                                              +"\n"+
								"        cepext =66677;"                                                 +"\n"+
								""                                                                     +"\n"+
								"    int cepext_length = strlen(cepext);//NPD, FP"                     +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"OK"
								,
					},
					//////////////////////////  125   修改函数摘要，使之添加函数间路径条件///////////////////	
					{
						"#include<string.h>"                                                   +"\n"+
								"#define A 1"                                                          +"\n"+
								"#define B 2"                                                          +"\n"+
								"int f1(int n, char*s)"                                                +"\n"+
								"{"                                                                    +"\n"+
								"    int x;"                                                           +"\n"+
								"    switch(n)"                                                        +"\n"+
								"    {"                                                                +"\n"+
								"        case A:"                                                      +"\n"+
								"             x = strlen(s);"                                          +"\n"+
								"             break;"                                                  +"\n"+
								"        case B:"                                                      +"\n"+
								"             x = -1;"                                                 +"\n"+
								"             break;"                                                  +"\n"+
								"    }"                                                                +"\n"+
								"    return x;"                                                        +"\n"+
								"}"                                                                    +"\n"+
								"void f()"                                                             +"\n"+
								"{"                                                                    +"\n"+
								"     f1(B, 0); //FP"                                                  +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					//////////////////////////  126 ///////////////////////	
					{
						"#include<stdio.h>"                                                    +"\n"+
								"int host_endian(void)"                                                +"\n"+
								"{"                                                                    +"\n"+
								"    FILE *fp;"                                                        +"\n"+
								"    char *file;"                                                      +"\n"+
								"    file = \"/tmp/__EnDiAn_TeSt__\";"                                   +"\n"+
								""                                                                     +"\n"+
								"    if ((fp = fopen(file, \"wb\")) == NULL) //FP"                       +"\n"+
								"        return -1;"                                                   +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"OK"
								,
					},
					//////////////////////////  127   没看明白。。。////////////////////////////	
					//JDH  需要修改,从摘要库中提取
					// strtok函数比较特殊。首次调用时，第一个参数s指向要分解的字符串，之后再次调用要把s设成NULL。
					{
						"#include<stdlib.h>"                                                   +"\n"+
								"#include<string.h>"                                                   +"\n"+
								"/*char *strtok(char *s, const char *delim);"                          +"\n"+
								"分解字符串为一组字符串。s为要分解的字符串，delim为分隔符字符串。"                                  +"\n"+
								"首次调用时，s指向要分解的字符串，之后再次调用要把s设成NULL。*/"                                  +"\n"+
								"static float params[2] = { 1.0f, 6800.0f };"                          +"\n"+
								"void f()"                                                             +"\n"+
								"{"                                                                    +"\n"+
								"    char *tok;"                                                       +"\n"+
								"    char *seps = \" \\t\";"                                              +"\n"+
								"    char temp_param_str[70];"                                        +"\n"+
								"    int param_index = 0;"                                             +"\n"+
								"    "                                                                 +"\n"+
								"    tok = strtok(temp_param_str, seps);"                              +"\n"+
								"    while (tok != NULL) {"                                            +"\n"+
								"        params[param_index++] = (float) atof(tok);"                   +"\n"+
								"        tok = strtok(NULL, seps);//FP, NPD, 方法\"strtok\"的第1 个参数"        +"\n"+
								"        if (param_index >= 2) {"                                      +"\n"+
								"            break;"                                                   +"\n"+
								"        }"                                                            +"\n"+
								"    }"                                                                +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},
					//////////////////////////  128   /////////////////////////
					{
						"#include <time.h>"                                                    +"\n"+
								"#include <stdio.h>"                                                   +"\n"+
								"int ghx_npd_16_f15 ()"                                                +"\n"+
								"{"                                                                    +"\n"+
								"  time_t rawtime;"                                                    +"\n"+
								"  struct tm * timeinfo;"                                              +"\n"+
								"  int year, month ,day;"                                              +"\n"+
								"  char * weekday[] = { \"Sunday\", \"Monday\",\"Tuesday\", \"Wednesday\",\"Thursday\", \"Friday\", \"Saturday\"};"+"\n"+
								""                                                                     +"\n"+
								"  printf (\"Enter year: \"); scanf (\"%d\",&year);"                       +"\n"+
								"  printf (\"Enter month: \"); scanf (\"%d\",&month);"                     +"\n"+
								"  printf (\"Enter day: \"); scanf (\"%d\",&day);"                         +"\n"+
								""                                                                     +"\n"+
								"  time ( &rawtime );"                                                 +"\n"+
								"  timeinfo = localtime ( &rawtime );"                                 +"\n"+
								"  timeinfo->tm_year = year - 1900;"                                   +"\n"+
								"  timeinfo->tm_mon = month - 1;"                                      +"\n"+
								"  timeinfo->tm_mday = day;"                                           +"\n"+
								"  mktime ( timeinfo );//FP"                                           +"\n"+
								""                                                                     +"\n"+
								"  printf (\"That day is a %s.\\n\", weekday[timeinfo->tm_wday]);"        +"\n"+
								"  "                                                                   +"\n"+
								"  return 0;"                                                          +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"OK"
								,
					},
					/////////////////////////////  129   /////////////////////////////	
					//摘要的问题，在对func2函数加摘要的时候只加入了ptr非空。应该再加入一点约束信息
					//       ---------聂敏慧
					{
						"#include <stdio.h>"                                                   +"\n"+
								""                                                                     +"\n"+
								"void func2(int *ptr, int val)"                                        +"\n"+
								"{"                                                                    +"\n"+
								"	if (val) {"                                                          +"\n"+
								"		*ptr = 2;"                                                          +"\n"+
								"	} else {"                                                            +"\n"+
								"		val++;"                                                             +"\n"+
								"	}"                                                                   +"\n"+
								"}"                                                                    +"\n"+
								""                                                                     +"\n"+
								"void func1()"                                                         +"\n"+
								"{"                                                                    +"\n"+
								"	func2(NULL, 0); //FP"                                                +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},

					/////////////////////////  130   ///////////////////	
					//模式中的错误，在ferror（stream）没有创建实例，可以修改。
					//        ------聂敏慧
					//处理不了，编译后已经将库函数ferror()展开   nmh
					{
						"#include <stdio.h>"                                                   +"\n"+
								"int jhb_npd_18_f1(void){"                                             +"\n"+
								"	FILE *stream;"                                                       +"\n"+
								"	stream = fopen(\"DUMMY.FIL\", \"w\");"                                   +"\n"+
								"	if (ferror(stream))       //DEFECT"                                  +"\n"+
								"	{"                                                                   +"\n"+
								"		printf(\"Error reading from DUMMY.FIL\\n\");"                          +"\n"+
								"//		clearerr(stream);"                                                +"\n"+
								"	}"                                                                   +"\n"+
								"//	fclose(stream);"                                                   +"\n"+
								"	return 0;"                                                           +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"NPD_PRE"
								,
					},		
					/////////////////  131   ///////////////////	
					{
						"#include <string.h>"                                                 +"\n"+
								"#include <stdio.h>"                                                   +"\n"+
								""                                                                     +"\n"+
								"void f(char* s){"                                                     +"\n"+
								"	if(s){"                                                              +"\n"+
								"		strchr(s,'w');"                                                   +"\n"+
								"	}"                                                                   +"\n"+
								"    "                                                                 +"\n"+
								"}"                                                                    
								,
								"gcc"
								,
								"OK"
								,
					},
					/////////////////  132   ///////////////////
					//这种暂时修改不了。因为在s = strchr(s,'w')这个节点，将s又赋值为了NULL_OR_NOTNULL
					{
						"#include <string.h>"                                                 +"\n"+
								"#include <stdio.h>"                                                   +"\n"+
								""                                                                     +"\n"+
								"void f(char* s){"                                                     +"\n"+
								"	if(s){"                                                              +"\n"+
								"		s=strchr(s,'w');"                                                   +"\n"+
								"	}"                                                                   +"\n"+
								"    "                                                                 +"\n"+
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
