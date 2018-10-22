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
public class NPD extends ModelTestBase {
	public NPD(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/NPD-0.1.xml";
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
				/////////////////  0 //////  本身这个测试用例就有问题，未初始化指针就直接调用？ ///////////////////	
				{
					""                                                                     +"\n"+
							"int* func2_1(int *a){"                                                +"\n"+
							"	return a;"                                                           +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int* func2_2(int* b) {"                                               +"\n"+
							"	return (void*)0;"                                                    +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int* func2_3(int a, int* b) {"                                        +"\n"+
							"	if (a == 0) {"                                                       +"\n"+
							"		return (void*)0;"                                                   +"\n"+
							"	} else {"                                                            +"\n"+
							"		return b;"                                                          +"\n"+
							"	}"                                                                   +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int func2_4()"                                                        +"\n"+
							"{"                                                                    +"\n"+
							"	int a = 1;"                                                          +"\n"+
							"	int b;"                                                              +"\n"+
							"	int* p;"                                                             +"\n"+
							"	p = func2_2(p);"                                                     +"\n"+
							"	b = *p;  //DEFECT,NPD,p"                                             +"\n"+
							"	return 0;"                                                           +"\n"+
							"}"                                                                    +"\n"
							,
							"gcc"
							,
							"NPD"
							,
				},			
				/////////////////  1   ///////////////////	
				{
					""                                                         +"\n"+
							"int intra5(int* x) {"                                                 +"\n"+
							"if (x != (void*)0) {"                                                 +"\n"+
							"return *x;  //FP,NPD"                                                 +"\n"+
							"} "                                                                   +"\n"+
							"return 0;"                                                            +"\n"+
							"}"                                                                    +"\n"+
							""                                                                   
							,
							"gcc"
							,
							"OK"
							,
				},
			
				
				
				
				/////////////////  2   ///////////////////	
				{
					""                                                        +"\n"+
							"int* x;"                                                              +"\n"+
							"int intra6() {"                                                       +"\n"+
							"if (x == (void*)0) {"                                                 +"\n"+
							"int* y = x;"                                                          +"\n"+
							"return *y; //DEFECT,NPD,y"                                            +"\n"+
							"}"                                                                    +"\n"+
							"return 0;"                                                            +"\n"+
							"}"                                                                    +"\n"+
							""                                                                   
							,
							"gcc"
							,
							"NPD"
							,
				},
				

				/////////////////  3   ///////////////////	
				{
					" "                                                       +"\n"+
							"	void f(){"                                                           +"\n"+
							"	int* t=h();"                                                         +"\n"+
							"		if(t!=(void*)0||*t==0){  //DEFECT,NPD,t"                            +"\n"+
							"			"                                                                  +"\n"+
							"		}"                                                                  +"\n"+
							"		"                                                                   +"\n"+
							"	}"                                                                   +"\n"+
							"	int* h(){"                                                           +"\n"+
							"		return (int*)0;"                                                   +"\n"+
							"	}"                                                                   +"\n"+
							""                                                                   
							,
							"gcc"
							,
							"NPD"
							,
				},
				
				/////////////////  4   ///////////////////////	
				{
					""                                                        +"\n"+
							"	void f(int* s){"                                                     +"\n"+
							"		int* p=(void*)0;"                                                   +"\n"+
							"		g(p,s);  //FP,NPD"                                                  +"\n"+
							"	}"                                                                   +"\n"+
							"	void g(int* s,int* p){"                                              +"\n"+
							"		if(s==(void*)0){"                                                   +"\n"+
							"			return ;"                                                          +"\n"+
							"		}"                                                                  +"\n"+
							"		if (s == p){"                                                       +"\n"+
							"			return;"                                                           +"\n"+
							"		}"                                                                  +"\n"+
							"		int d=*s;  //FP,NPD"                                                +"\n"+
							"	}"                                                                   +"\n"+
							""                                                                   
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////  5   ///////////////////	
				{
					""                                                        +"\n"+
							"	void f(int* s){"                                                     +"\n"+
							"		int* p=(void*)0;"                                                   +"\n"+
							"		g(p,s);  //FP,NPD"                                                  +"\n"+
							"	}"                                                                   +"\n"+
							"	void g(int* s,int* p){"                                              +"\n"+
							"		if(s==(void*)0){"                                                   +"\n"+
							"			return ;"                                                          +"\n"+
							"		}"                                                                  +"\n"+
							"		if (*s == 1){"                                                      +"\n"+
							"			return;"                                                           +"\n"+
							"		}"                                                                  +"\n"+
							"		int d=*s;;  //FP,NPD"                                               +"\n"+
							"	}"                                                                   +"\n"+
							""                                                                   
							,
							"gcc"
							,
							"OK"
							,
				},
				
				/////////////////  6   ///////////////////	
				{
					""                                                        +"\n"+
							"	int* p;"                                                             +"\n"+
							"	void f(){"                                                           +"\n"+
							"		p=(void*)0;"                                                        +"\n"+
							"		g(); "                                                              +"\n"+
							"	}"                                                                   +"\n"+
							"	void g(){"                                                           +"\n"+
							"		int i=0;"                                                           +"\n"+
							"		if(i>0){"                                                           +"\n"+
							"			i++;"                                                              +"\n"+
							"			i++;"                                                              +"\n"+
							"			i++;"                                                              +"\n"+
							"			int a=*p;  //FP,NPD"                                               +"\n"+
							"		}"                                                                  +"\n"+
							"	}"                                                                   +"\n"+
							""                                                                   
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////  7   ///////////////////	
				{
					""                                                        +"\n"+
							"	void f(int* p,int* q){"                                              +"\n"+
							"		if(q==(void*)0){"                                                   +"\n"+
							"			return;"                                                           +"\n"+
							"		}"                                                                  +"\n"+
							"		if(p==q){"                                                          +"\n"+
							"			int a=*p;  //FP,NPD"                                               +"\n"+
							"		}"                                                                  +"\n"+
							"		//int a=*p;"                                                        +"\n"+
							"	}"                                                                   +"\n"+
							""                                                                   
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////  8   ///////////////////	
				{
					""                                                       +"\n"+
							"	void f(int* p,int* q){"                                              +"\n"+
							"		if(q!=(void*)0){"                                                   +"\n"+
							"			return;"                                                           +"\n"+
							"		}"                                                                  +"\n"+
							"		if(p==q){"                                                          +"\n"+
							"			//int a=*p;"                                                       +"\n"+
							"		}else{"                                                             +"\n"+
							"			int a=*p; //FP,NPD"                                                +"\n"+
							"		}"                                                                  +"\n"+
							"	}"                                                                   +"\n"+
							""                                                                     +"\n"+
							""                                                                   
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////  9   ///////////////////	
				{
					""                                                       +"\n"+
							"	void f(int* p,int* q){"                                              +"\n"+
							"		if(q!=(void*)0){"                                                   +"\n"+
							"			return;"                                                           +"\n"+
							"		}"                                                                  +"\n"+
							"		if(p!=q){"                                                          +"\n"+
							"			int a=*p;  //FP,NPD"                                               +"\n"+
							"		}else{"                                                             +"\n"+
							"			//int a=*p;"                                                       +"\n"+
							"		}"                                                                  +"\n"+
							"	}"                                                                   +"\n"+
							""                                                                     +"\n"+
							""                                                                   
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////  10   ///////////////////	
				{
					""                                                       +"\n"+
							"	void f(){"                                                           +"\n"+
							"	int* t=g();"                                                         +"\n"+
							"		if(0>1|| *t>0){ //DEFECT,NPD,t"                                     +"\n"+
							"		}"                                                                  +"\n"+
							"	}	"                                                                  +"\n"+
							"	int* g(){"                                                           +"\n"+
							"		return (void*)0;"                                                   +"\n"+
							"	}"                                                                   +"\n"+
							""                                                                   
							,
							"gcc"
							,
							"NPD"
							,
				},
				/////////////////  11   ///////////////////	
				{
					""                                                       +"\n"+
							"	void f(){"                                                           +"\n"+
							"	int* t=g();"                                                         +"\n"+
							"		if(*t>0 && 0<1){ //DEFECT,NPD,t"                                    +"\n"+
							"		}"                                                                  +"\n"+
							"	}	"                                                                  +"\n"+
							"	int* g(){"                                                           +"\n"+
							"		return (void*)0;"                                                   +"\n"+
							"	}"                                                                   +"\n"+
							""                                                                   
							,
							"gcc"
							,
							"NPD"
							,
				},
				/////////////////  12   ///////////////////	
				{
					"#include <string.h>"                                                  +"\n"+
							"#include <stdlib.h>"                                                  +"\n"+
							"#include <assert.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"int test_fp_1(const char *str, const char *suffix)"                   +"\n"+
							"{"                                                                    +"\n"+
							"    int str_len, suffix_len;"                                         +"\n"+
							""                                                                     +"\n"+
							"    str_len = strlen(str);"                                           +"\n"+
							"    suffix_len = strlen(suffix);"                                     +"\n"+
							"    if (str_len < suffix_len)"                                        +"\n"+
							"        return -1;  /* str is shorter than suffix */"                 +"\n"+
							"    return strcmp(str + str_len - suffix_len, suffix); //FP,NPD"      +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int test_fp_3(int* p)"                                                +"\n"+
							"{"                                                                    +"\n"+
							"	if (p == 0) {"                                                       +"\n"+
							"		abort();"                                                           +"\n"+
							"	}"                                                                   +"\n"+
							"	*p = 1; //FP,NPD"                                                    +"\n"+
							"	return 0;"                                                           +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int test_fp_4(int* p)"                                                +"\n"+
							"{"                                                                    +"\n"+
							"	if (p == 0) {"                                                       +"\n"+
							"		int a = 1;"                                                         +"\n"+
							"		exit(a);"                                                           +"\n"+
							"	}"                                                                   +"\n"+
							"	*p = 1;  //FP,NPD"                                                   +"\n"+
							"	return 0;"                                                           +"\n"+
							"}	"                                                                   +"\n"+
							""                                                                     +"\n"+
							"void error_fp() {"                                                    +"\n"+
							"	abort();"                                                            +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int test_fp_5(int* p) "                                               +"\n"+
							"{"                                                                    +"\n"+
							"	if (p == 0) {"                                                       +"\n"+
							"		error_fp();"                                                        +"\n"+
							"	}"                                                                   +"\n"+
							"	*p = 1;  //FP,NPD"                                                   +"\n"+
							"	return 0;"                                                           +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////  13   ///////////////////	
				{
					        "#include <assert.h>"                                                  +"\n"+
							"int test_fp_6(int* a)"                                                +"\n"+
							"{"                                                                    +"\n"+
							"	int b = 1;"                                                          +"\n"+
							"	a = (int*)malloc(1);"                                           +"\n"+
							"	assert(a!=0);"                                                       +"\n"+
							"	b = *a;  //FP,NPD"                                                   +"\n"+
							"	free(a);"                                                            +"\n"+
							"	return 0;"                                                            +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void fun_fp_7(){"                                                     +"\n"+
							"	return;"                                                            +"\n"+
							""                                                                     +"\n"+
							"}"                                                                    +"\n"+
							"void test_fp_7(char *p){"                                             +"\n"+
							"	if(!p)"                                                              +"\n"+
							"		fun_fp_7();"                                                        +"\n"+
							"	*p='a';//NPD"                                                     +"\n"+
							"}"
							,
							"gcc"
							,
							"NPD"
							,
				},
				/////////////////  14  ///////////////////	
				{
					"typedef struct sa {"                                                  +"\n"+
							"	int a;"                                                              +"\n"+
							"} SA;"                                                                +"\n"+
							""                                                                     +"\n"+
							"SA* func1(int i, SA* sb) {"                                           +"\n"+
							"	if ( i == 0) {"                                                      +"\n"+
							"		return (void*)0;"                                                   +"\n"+
							"	}"                                                                   +"\n"+
							"	return sb;"                                                          +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int func2() {"                                                        +"\n"+
							"	SA* sa = func1(1, (void*)0);"                                        +"\n"+
							"	if (sa != (void*)0) {		"                                             +"\n"+
							"		(sa)->a= 1;  //FP,NPD"                                              +"\n"+
							"	}"                                                                   +"\n"+
							"	return 0;"                                                           +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////  15   ///////////////////	
				{
					"static void func3(raw1)"                                              +"\n"+
							"register unsigned long *raw1;"                                        +"\n"+
							"{"                                                                    +"\n"+
							"        register unsigned long *cook, *raw0;"                         +"\n"+
							"        unsigned long dough[32];"                                     +"\n"+
							"        register int i;"                                              +"\n"+
							""                                                                     +"\n"+
							"        cook = dough;"                                                +"\n"+
							"        for( i = 0; i < 16; i++, raw1++ ) {"                          +"\n"+
							"								raw0 = raw1++;"                                               +"\n"+
							"                *cook    = (*raw0 & 0x00fc0000L) << 6;  //FP,NPD"     +"\n"+
							"				}"                                                                +"\n"+
							"        return;"                                                      +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},

				/////////////////  16   ///////////////////	
				{
					""                                                                     +"\n"+
							"int* func11_1(int *a){"                                               +"\n"+
							"	return a;"                                                           +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int* func11_2(int* b) {"                                              +"\n"+
							"	return (void*)0;"                                                    +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int* func11_3(int a, int* b) {"                                       +"\n"+
							"	if (a == 0) {"                                                       +"\n"+
							"		return (void*)0;"                                                   +"\n"+
							"	} else {"                                                            +"\n"+
							"		return b;"                                                          +"\n"+
							"	}"                                                                   +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int test11_1()"                                                       +"\n"+
							"{"                                                                    +"\n"+
							"	int a = 1;"                                                          +"\n"+
							"	int b;"                                                              +"\n"+
							"	int* p;"                                                             +"\n"+
							"	p = &a;"                                                           +"\n"+
							"	p = func11_1(p); //FP,NPD"                                           +"\n"+
							"	b = *p;"                                                           +"\n"+
							"	p = func11_2(p);"                                                    +"\n"+
							"	b = *p;   //DEFECT,NPD,p"                                            +"\n"+
							"	return 0;"                                                           +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int test11_2()"                                                       +"\n"+
							"{"                                                                    +"\n"+
							"	int a = 1;"                                                          +"\n"+
							"	int b;"                                                              +"\n"+
							"	int* p;"                                                             +"\n"+
							"	p = func11_3(1, p); //FP,NPD"                                        +"\n"+
							"	b = *p;  //DEFECT,NPD,p"                                             +"\n"+
							"	return 0;"                                                           +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"NPD"
							,
				},				            
				/////////////////  17   ///////////////////	
				{
					"typedef struct _ST {"                                                 +"\n"+
							"    int a;"                                                           +"\n"+
							"}ST;"                                                                 +"\n"+
							"void* malloc(int size);"                                              +"\n"+
							"void free(void* ptr);"                                                +"\n"+
							""                                                                     +"\n"+
							"int func(ST* st)"                                                     +"\n"+
							"{"                                                                    +"\n"+
							"    ST *sa = (ST*)malloc(sizeof(ST));"                                +"\n"+
							"    if (sa != ((void *)0) ) {"                                        +"\n"+
							"       sa->a = 1; //FP,NPD"                                           +"\n"+
							"       free(sa);"                                                     +"\n"+
							"       return 1;"                                                     +"\n"+
							"    }"                                                                +"\n"+
							"    free(sa);"                                                        +"\n"+
							"    return 0;"                                                        +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},				            
				
				/////////////////  18   ///////////////////	
				{
					"struct sa{"                                                           +"\n"+
							"	int* p;	"                                                            +"\n"+
							"	int a;"                                                              +"\n"+
							"};"                                                                   +"\n"+
							"void test4(struct sa *stream)"                                        +"\n"+
							"{"                                                                    +"\n"+
							"	int a=0;"                                                            +"\n"+
							"  if(stream){"                                                        +"\n"+
							"    stream->a= 0;"                                                    +"\n"+
							"  }else{	"                                                            +"\n"+
							"  	a=2;    //FP,NPD"                                                  +"\n"+
							"  }"                                                                  +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				
				
				/////////////////  19   ///////////////////	
				{
							"	int * func() {"                                                      +"\n"+
							"		return 0;"                                                          +"\n"+
							"	}"                                                                   +"\n"+
							""                                                                   +"\n"+
							""                                                                     +"\n"+
							""                                                         +"\n"+
							"	int func1()"                                                 +"\n"+
							"	{"                                                                   +"\n"+
							"		int *p;"                                                            +"\n"+
							"		p = func();"                                                    +"\n"+
							"		*p = 1;  //DEFECT,NPD,p"                                            +"\n"+
							"	}	"                                                                  +"\n"+
							""                                                                   
							,
							"gcc"
							,
							"NPD"
							,
				},
				/////////////////  20   ///////////////////	
				{
							"#include <stdlib.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"void func_20_2(){"                                                    +"\n"+
							"	int i;"                                                              +"\n"+
							"	for(i=1;i<10;i++){"                                                  +"\n"+
							"		char* ch=(char*)malloc(1);"                                         +"\n"+
							"		*ch='1'; //DEFECT,NPD,ch"                                           +"\n"+
							"	}"                                                                   +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void func_20_3(int a, int b, int k)"                                  +"\n"+
							"{"                                                                    +"\n"+
							"	int c;"                                                              +"\n"+
							"	char* p = (char*)malloc(1);"                                         +"\n"+
							"	if (a != 4)"                                                         +"\n"+
							"		c = p[0]; //DEFECT,NPD,p"                                           +"\n"+
							"	c += *p;//FP, NPD"                                                   +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"NPD"
							,
				},
				/////////////////  21   ///////////////////	
				{
					"typedef struct _ST {"                                                 +"\n"+
							"    char a;"                                                          +"\n"+
							"}ST;"                                                                 +"\n"+
							"int func(ST* st)"                                                     +"\n"+
							"{"                                                                    +"\n"+
							"    ST *sa = (ST*)st;"                                                +"\n"+
							"    if (sa == ((void *)0) || sa->a == 'w') { //FP,NPD"                +"\n"+
							"       return 1;"                                                     +"\n"+
							"    }"                                                                +"\n"+
							"    return 0;"                                                        +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////  22   ///////////////////	
				{
					"#include <assert.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"int func(int* a)"                                                     +"\n"+
							"{"                                                                    +"\n"+
							"    assert(a!=0);"                                                    +"\n"+
							"    *a = 1;  //FP,NPD"                                                +"\n"+
							"    return 0;"                                                        +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////  23   ///////////////////	
				{
					"#include <assert.h>"                                                  +"\n"+
							"typedef struct _st {"                                                 +"\n"+
							"	int a;"                                                              +"\n"+
							"}ST;"                                                                 +"\n"+
							"void test1(ST* st, int c) {"                                          +"\n"+
							"	int b;"                                                              +"\n"+
							"	if (st == 0 || c ==1) {"                                             +"\n"+
							"		b = (*st).a;  //DEFECT,NPD,st"                                      +"\n"+
							"	}"                                                                   +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"NPD"
							,
				},
				/////////////////  24   ///////////////////	
				{
					"void func1(void* ptr) {"                                              +"\n"+
							"	char* net =  (char*) (ptr);"                         +"\n"+
							"	*net = '1';"                                                         +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void func2(void* ptr) {"                                              +"\n"+
							"	char* net = (char*)ptr; //FP,NPD"                                    +"\n"+
							"	*net = '1'; //FP,NPD"                                                +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void func3() {"                                                       +"\n"+
							"	void *ptr = (void*)0;"                                               +"\n"+
							"	char* net = (char*) (ptr);"                         +"\n"+
							"	*net = '1';  //DEFECT,NPD,net"                                       +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void func4() {"                                                       +"\n"+
							"	void *ptr = (void*)0;"                                               +"\n"+
							"	char* net = (char*)ptr;"                                             +"\n"+
							"	*net = '1';  //DEFECT,NPD,net"                                       +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"NPD"
							,
				},
				/////////////////  25   ///////////////////	
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"#include <string.h>"                                                  +"\n"+
							"struct ghx_npd_5_s5"                                                  +"\n"+
							"{"                                                                    +"\n"+
							"	char* ss;"                                                           +"\n"+
							"	"                                                                    +"\n"+
							"};"                                                                   +"\n"+
							"void ghx_npd_5_f5()"                                                  +"\n"+
							"{"                                                                    +"\n"+
							"	struct ghx_npd_5_s5 s;"                                                     +"\n"+
							"	s.ss=(char*)malloc(10);"                                             +"\n"+
							"	char* a=(char*)malloc(10);"                                          +"\n"+
							"	s.ss[0]=*a;//DEFECT"                                                 +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"NPD"
							,
				},

				/////////////////  26   ///////////////////	
				{
					"#include <stddef.h>"                                                  +"\n"+
							"int *p;"                                                              +"\n"+
							"int jhb_npd_8_f1(int *i){"                                            +"\n"+
							"	i=NULL;"                                                             +"\n"+
							"	return 0;"                                                           +"\n"+
							"}"                                                                    +"\n"+
							"void jhb_npd_8_f2(){"                                                 +"\n"+
							"	int t;"                                                              +"\n"+
							"	t=jhb_npd_8_f1(p);"                                                  +"\n"+
							"	t=*p;       //DEFECT"                                                +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////  27   ///////////////////	
				{
					"#include <stdio.h>"                                                   +"\n"+
							"#include <math.h>"                                                    +"\n"+
							"int ghx_npd_17_f16() "                                                +"\n"+
							"{ "                                                                   +"\n"+
							"double fraction, integer; "                                           +"\n"+
							"double number = 100000.567; "                                         +"\n"+
							"fraction = modf(number, &integer); //FP"                              +"\n"+
							"printf(\"The whole and fractional parts of %lf are %lf and %lf\\n\", "   +"\n"+
							"number, integer, fraction); "                                         +"\n"+
							"return 0; "                                                           +"\n"+
							"} "                                                                   
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////  28   ///////////////////	
				{
					"#include <stdio.h>"                                                   +"\n"+
							"#include <stdlib.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"int ghx_npd_10_f10 ()"                                                +"\n"+
							"{"                                                                    +"\n"+
							"  int i;"                                                             +"\n"+
							"  char * buffer;"                                                     +"\n"+
							"  scanf (\"%d\", &i);"                                                  +"\n"+
							""                                                                     +"\n"+
							"  buffer = (char*) malloc (i+1);"                                     +"\n"+
							""                                                                     +"\n"+
							"  buffer[i]='\\0';//DEFECT"                                            +"\n"+
							"  printf (\"%s\\n\",buffer);"                                            +"\n"+
							"  free (buffer);"                                                     +"\n"+
							""                                                                     +"\n"+
							"  return 0;"                                                          +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"NPD"
							,
				},
				/////////////////  29   ///////////////////	
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
							"}"                                                                    
							,
							"gcc"
							,
							"NPD"
							,
				},
				/////////////////  30   ///////////////////	
				{
					"#include <string.h>"                                                  +"\n"+
							"#include <stdio.h>"                                                   +"\n"+
							"int ghx_npd_11_f10 ()"                                                +"\n"+
							"{"                                                                    +"\n"+
							"  char * pch;"                                                        +"\n"+
							"  char str[] = \"Example string\";"                                     +"\n"+
							"  int i=1;"                                                           +"\n"+
							"  pch = (char*) memchr (str, 'p', strlen(str));//FP"                  +"\n"+
							"  if (pch!=NULL)"                                                     +"\n"+
							"    printf (\"'p' found at position %d.\\n\", pch-str+1);"               +"\n"+
							"  else"                                                               +"\n"+
							"    pch[i]=0;//NPD"                                                    +"\n"+
							"  return 0;"                                                          +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"NPD"
							,
				},
				/////////////////  31   ///////////////////	
				{
					"#include <stdlib.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"void func()"                                                          +"\n"+
							"{"                                                                    +"\n"+
							"	int i = 1;"                                                          +"\n"+
							"	char *ptr;"                                                          +"\n"+
							""                                                                     +"\n"+
							"	ptr = (char*)malloc(i+1);"                                           +"\n"+
							"	ptr[i]='\\0';//DEFECT"                                                +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"NPD"
							,
				},
				/////////////////  32   ///////////////////	
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"#include <string.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"void func()"                                                          +"\n"+
							"{"                                                                    +"\n"+
							"	char str[] = \"string\";"                                              +"\n"+
							"	char *ptr;"                                                          +"\n"+
							"	char tmp;"                                                           +"\n"+
							""                                                                     +"\n"+
							"	ptr = (char*)memchr(str,'p',strlen(str));"                           +"\n"+
							"	tmp = *ptr; //DEFECT"                                                +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"NPD"
							,
				},
				/////////////////  33   ///////////////////	
				{
					"  int global;"                                                        +"\n"+
							"  int *xmalloc() {"                                                   +"\n"+
							"    if (global) return &global;"                                      +"\n"+
							"    return 0; // xmalloc() may return NULL"                           +"\n"+
							"  }"                                                                  +"\n"+
							"  "                                                                   +"\n"+
							"  void npd_func_must(int flag, char *arg) {"                          +"\n"+
							"    int *p = xmalloc(); // xmalloc() may return NULL"                 +"\n"+
							"   *p = 1;  // DEFECT"                                                +"\n"+
							" }"                                                                   
							,
							"gcc"
							,
							"NPD"
							,
				},	
				/////////////////  34   ///////////////////	
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"#include <string.h>"                                                  +"\n"+
							"struct ghx_npd_5_s5"                                                  +"\n"+
							"{"                                                                    +"\n"+
							"	char* ss;"                                                           +"\n"+
							"	"                                                                    +"\n"+
							"};"                                                                   +"\n"+
							"void ghx_npd_5_f5()"                                                  +"\n"+
							"{"                                                                    +"\n"+
							"	struct ghx_npd_5_s5 s;"                                                     +"\n"+
							"	s.ss=(char*)malloc(10);"                                             +"\n"+
							"	char* a=(char*)malloc(10);"                                          +"\n"+
							"	s.ss[0]=*a;//DEFECT"                                                 +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"NPD"
							,
				},

				/////////////////  35   ///////////////////	
				{
					"   void deref(int *p){"                                               +"\n"+
							"   	  *p = *p + 10;"                                                  +"\n"+
							"   }"                                                                 +"\n"+
							"  "                                                                   +"\n"+
							"   void rnpd_2(int *t){"                                              +"\n"+
							"  	  deref(t); //DEFECT"                                              +"\n"+
							"  	  if (!t) return;"                                                 +"\n"+
							"     *t ++;"                                                          +"\n"+
							"  }"                                                                  
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////  36   ///////////////////	
				{
					"  void rnpd_1(int* t, int v) {"                                       +"\n"+
							"      *t = 0;  // DEFECT"                                             +"\n"+
							"      if (v < 0) v = -v;"                                             +"\n"+
							"      if (t) *t = v;  // t is verified before dereference"            +"\n"+
							"  }"                                                                  
							,
							"gcc"
							,
							"OK"
							,
				},
				
				
				/////////////////  37   ///////////////////	
				{
					//在i = 1~9时有空指针IP
					" #include <stdlib.h>"                                                 +"\n"+
							" void npd_func_might(int flag, char *arg) {"                          +"\n"+
							"   char *p = arg;"                                                    +"\n"+
							"   int i;"                                                            +"\n"+
							"   for(i=0;i<10;i++){"                                                +"\n"+
							"      *p;"                                                   +"\n"+
							"      p=(char*)malloc(10);"                                           +"\n"+
							"   }"                                                                 +"\n"+
							" "                                                                    +"\n"+
							" }"                                                                   
							,
							"gcc"
							,
							"NPD"
							,
				},
				/////////////////  38   ///////////////////	
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"#define SIZE 10"                                                      +"\n"+
							""                                                                     +"\n"+
							"char* ckd_malloc(int len)"                                            +"\n"+
							"{"                                                                    +"\n"+
							"	char *ptr;"                                                          +"\n"+
							""                                                                     +"\n"+
							"	ptr = (char*)malloc(len * sizeof(char));"                            +"\n"+
							""                                                                     +"\n"+
							"	if (!ptr)"                                                           +"\n"+
							"		exit(-1);"                                                          +"\n"+
							"	else"                                                                +"\n"+
							"		return ptr;"                                                        +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void func(char *var)"                                                 +"\n"+
							"{"                                                                    +"\n"+
							"	if (!var)"                                                           +"\n"+
							"		var = ckd_malloc(SIZE);"                                            +"\n"+
							""                                                                     +"\n"+
							"	var[0] = '\\0'; //FP"                                                 +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
			
				/////////////////  39   ///////////////////	
				{
					" #include <stdlib.h>"                                                 +"\n"+
							"  void npd_check_must(char *p) {"                                     +"\n"+
							"    if (p != NULL) { }"                                               +"\n"+
							"    p[0] = 0; //DEFECT"                                               +"\n"+
							"  }"                                                                  
							,
							"gcc"
							,
							"NPD"
							,
				},
				/////////////////  40   ///////////////////	
				{
					"char func(char *var)"                                                 +"\n"+
							"{"                                                                    +"\n"+
							"	char buf = 'a';"                                                     +"\n"+
							""                                                                     +"\n"+
							"	if (!var)"                                                           +"\n"+
							"		var = &buf;"                                                        +"\n"+
							""                                                                     +"\n"+
							"	return *var; //FP"                                                   +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////  41   ///////////////////	
				{
					"#include<stdlib.h>"                                                   +"\n"+
							"#include<stdio.h>"                                                    +"\n"+
							"#define NELEMS(arr) (sizeof(arr) / sizeof(arr[0]))"                   +"\n"+
							"int numarray[] = {123, 145, 512, 627, 800, 933};"                     +"\n"+
							"int numeric (const int *p1, const int *p2){"                          +"\n"+
							"	return(*p1 - *p2);"                                                  +"\n"+
							"}"                                                                    +"\n"+
							"int jhb_npd_13_f1(int key){"                                          +"\n"+
							"int *itemptr;"                                                        +"\n"+
							"itemptr = (int *)bsearch (&key, numarray, NELEMS(numarray),"          +"\n"+
							"						  sizeof(int), (int(*)(const void *,const void *))numeric);"    +"\n"+
							"return (*itemptr) ;     //DEFECT"                                     +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"NPD"
							,
				},		
				/////////////////  42   ///////////////////	
				{
					"int *p;"                                                              +"\n"+
							"void f(){"                                                            +"\n"+
							"   p=0;"                                                              +"\n"+
							"}"                                                                    +"\n"+
							"void func()"                                                          +"\n"+
							"{"                                                                    +"\n"+
							"	f();"                                                                +"\n"+
							"	*p=1; //DEFECT ,NPD"                                                 +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"NPD"
							,
				},
				/////////////////  43   ///////////////////	
				{
					"void func(double *ptr)"                                               +"\n"+
							"{"                                                                    +"\n"+
							"	if (!ptr)"                                                           +"\n"+
							"		return;"                                                            +"\n"+
							""                                                                     +"\n"+
							"	*ptr = 2.0;"                                                         +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////  44   ///////////////////	
				{
					""                                                                     +"\n"+
							"void func1(int *var1, int *var2)"                                     +"\n"+
							"{"                                                                    +"\n"+
							"	if (!var1)"                                                          +"\n"+
							"		return;"                                                            +"\n"+
							"	if (!var2)"                                                          +"\n"+
							"		var2 = var1;"                                                       +"\n"+
							""                                                                     +"\n"+
							"	*var2 = 0; //FP"                                                     +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////  45   ///////////////////	
				{
					"#include <stdlib.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"#define get_new(type, num)  (type *)malloc(sizeof(type)*num)"         +"\n"+
							""                                                                     +"\n"+
							"int zk_npd_34_f1()"                                                   +"\n"+
							"{"                                                                    +"\n"+
							"	int *ptr;"                                                           +"\n"+
							""                                                                     +"\n"+
							"	ptr = get_new(int, 1);"                                              +"\n"+
							""                                                                     +"\n"+
							"	return *ptr; //DEFECT"                                               +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"NPD"
							,
				},

				/////////////////  46   ///////////////////	
				{
					"#include <stdlib.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"int* func1(int *var1, char *var2)"                                    +"\n"+
							"{"                                                                    +"\n"+
							"	if (var1 == NULL || var2 == NULL) {"                                 +"\n"+
							"		*var1 = 0; //DEFECT"                                                +"\n"+
							"		return NULL;"                                                       +"\n"+
							"	}"                                                                   +"\n"+
							"	return var1;"                                                        +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"NPD"
							,
				},
				/////////////////  47  测试用例有错误，IP存在漏报///////////////////	
				{
					""                                                       +"\n"+
							"	void f(int* p,int* q){"                                              +"\n"+
							"		if(q==(void*)0){"                                                   +"\n"+
							"			return;"                                                           +"\n"+
							"		}"                                                                  +"\n"+
							"		if(p!=q){"                                                          +"\n"+
							"			//int a=*p;"                                                       +"\n"+
							"		}else{"                                                             +"\n"+
							"			int a=*p; //FP,NPD"                                                +"\n"+
							"		}"                                                                  +"\n"+
							"	}"                                                                   +"\n"+
							""                                                                     +"\n"+
							""                                                                   
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////  48   这malloc到底应该怎么判断？与用例3对比最后的处理方式不同///////////////////	
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"void test2_3(char* data) {"                                           +"\n"+
							"	data = data ? (char*)realloc(data,10) : (char*)malloc(10);"          +"\n"+
							"	*data = 'c';"                                                        +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"NPD"
							,
				},
				///////////////////////////  49   ///////////////////	
				{
					""                                                                     +"\n"+
							"typedef struct sa {"                                                  +"\n"+
							"   int a;"                                                            +"\n"+
							"}SA;"                                                                 +"\n"+
							""                                                                     +"\n"+
							"typedef struct sb {"                                                  +"\n"+
							"   int b,a;"                                                          +"\n"+
							"   SA* c;"                                                            +"\n"+
							"}SB;"                                                                 +"\n"+
							""                                                                     +"\n"+
							"struct SC {"                                                          +"\n"+
							"   int d;"                                                            +"\n"+
							"};"                                                                   +"\n"+
							"int func(int a, SB* pb) {"                                            +"\n"+
							"    SA* pa;"                                                          +"\n"+
							"    for (pa = (SA*)pb->c; //FP,NPD"                                   +"\n"+
							"         pa->a < 2;//DEFECT NPD pa"                                                  +"\n"+
							"         pa->a++) {"                                                  +"\n"+
							"        if (pa->a == a) { //FP,NPD"                                   +"\n"+
							"            return 1;"                                                +"\n"+
							"        }"                                                            +"\n"+
							"    }"                                                                +"\n"+
							"    return 0;"                                                        +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////  50这个用例有点强大   ///////////////////
				//JDH  暂不修改
				{
							" "                                                                    +"\n"+
							"void RecordDBID(char* p,char* q){"                                    +"\n"+
							"	if(!p&&!q){}"                                                        +"\n"+
							"	else if(!p){"                                                        +"\n"+
							"		*q;//FP"                                                            +"\n"+
							"	}"                                                                   +"\n"+
							""                                                                     +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"NPD"
							,
				},
				/////////////////  51   不可达分支///////////////////	
				{
					"void func(int x){"                                                    +"\n"+
							"	char* p=0;"                                                          +"\n"+
							"	int y=1;"                                                            +"\n"+
							"	if(x>=1 && x<=5){"                                                   +"\n"+
							"		y=x;"                                                               +"\n"+
							"		if(x>y)"                                                            +"\n"+
							"			*p='1'; //FT"                                                      +"\n"+
							"	}"                                                                   +"\n"+
							"	if(x==0)"                                                            +"\n"+
							"		y=0;"                                                               +"\n"+
							"	if(x==1)"                                                            +"\n"+
							"		x=x/y;"                                                             +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////////////  52  可能是exit判断不对？////////////////////////	
				{
					"#include <stdio.h>"                                                   +"\n"+
							"#include <stdlib.h>"                                                  +"\n"+
							"int ghx_npd_10_f9 ()"                                                 +"\n"+
							"{"                                                                    +"\n"+
							"  int i;"                                                             +"\n"+
							"  char * buffer;"                                                     +"\n"+
							"  scanf (\"%d\", &i);"                                                  +"\n"+
							""                                                                     +"\n"+
							"  buffer = (char*) malloc (i+1);"                                     +"\n"+
							"  if (buffer==NULL) exit (1);"                                        +"\n"+
							""                                                                     +"\n"+
							"else"                                                                 +"\n"+
							"{"                                                                    +"\n"+
							"  buffer[i]='\\0';//FP"                                                +"\n"+
							""                                                                     +"\n"+
							"  printf (\"%s\\n\",buffer);"                                            +"\n"+
							"  free (buffer);"                                                     +"\n"+
							"}"                                                                    +"\n"+
							"  return 0;"                                                          +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				///////////////////////////  53  ///////////////////	
				//jdh  提醒周虹伯处理
				{
					""                                                                     +"\n"+
							"void func1()"                                                         +"\n"+
							"{"                                                                    +"\n"+
							"	int buf[10];"                                                        +"\n"+
							"	int *ptr;"                                                           +"\n"+
							""                                                                     +"\n"+
							"	ptr = (int*)((int)(&buf[0]) & ~3);"                                  +"\n"+
							"	*ptr = 3; //FP"                                                      +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				///////////////////////////  54  ///////////////////	
				{
					"#include <string.h>"                                                  +"\n"+
							"#include <stdio.h>"                                                   +"\n"+
							"void zk_npd_12_f2()"                                                  +"\n"+
							"{"                                                                    +"\n"+
							"	char str[] = \"This is sample\";"                                      +"\n"+
							"	char *pch;"                                                          +"\n"+
							""                                                                     +"\n"+
							"	pch = strstr(str, \"nothing\"); //FP"                                  +"\n"+
							"	*pch; //DEFECT"                                         +"\n"+
							"	return;"                                                             +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"NPD"
							,
				},
				/////////////////  55 ///////////////////	
				{
					"int* func2_3(int a, int* b) {"                                        +"\n"+
							"	if (a == 0) {"                                                       +"\n"+
							"		return (void*)0;"                                                   +"\n"+
							"	} else {"                                                            +"\n"+
							"		return b;"                                                          +"\n"+
							"	}"                                                                   +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int func2_5()"                                                        +"\n"+
							"{"                                                                    +"\n"+
							"	int a = 1;"                                                          +"\n"+
							"	int b;"                                                              +"\n"+
							"	int* p=&a;"                                                             +"\n"+
							"	p = func2_3(1, p);"                                                  +"\n"+
							"	b = *p; //FP,p"                                              +"\n"+
							"	return 0;"                                                           +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////////////// 56  /////////////////////////////	
				{
					"#include <stddef.h>"                                                  +"\n"+
							"#include <stdlib.h>"                                                  +"\n"+
							"int *p = (int*)malloc(4);"                                            +"\n"+
							"typedef struct{"                                                      +"\n"+
							"   int t;"                                                            +"\n"+
							"}S;"                                                                  +"\n"+
							"S* s;"                                                                +"\n"+
							"int f(){"                                                             +"\n"+
							"	s=NULL;"                                                             +"\n"+
							"	return 0;"                                                           +"\n"+
							"}"                                                                    +"\n"+
							"void main(){"                                                         +"\n"+
							""                                                                     +"\n"+
							"    f();"                                                             +"\n"+
							"    (s)->t;//DEFECT"                                                  +"\n"+
							"    "                                                                 +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"NPD"
							,
				},
				/////////////////  57   ///////////////////	
				{
					"#include <stdio.h>"                                                   +"\n"+
							"#include <stdlib.h>"                                                  +"\n"+
							"#include \"time.h\""                                                    +"\n"+
							"#include <math.h>"                                                    +"\n"+
							"int jhb_npd_29_f1(void){"                                             +"\n"+
							"	FILE* f;"                                                            +"\n"+
							"	f=freopen(\"OUTPUT.FIL\", \"w\", stdout);"                               +"\n"+
							"	*f;                               //DEFECT"                          +"\n"+
							"	fclose(stdout);"                                                     +"\n"+
							"	return 0;"                                                           +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"NPD"
							,
				},
				////////////////////////////58//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"#include <string.h>"                                                  +"\n"+
							"#include <stdio.h>"                                                   +"\n"+
							""                                                                     +"\n"+
							"void test5_1(int b){"                                                 +"\n"+
							"	int i,j;"                                                              +"\n"+
							"	for(i=1;i<10;i++){"                                                  +"\n"+
							"		char* ch1=(char*)malloc(b);"                                        +"\n"+
							"		char* ch2=(char*)malloc(b);"                                        +"\n"+
							"		for (j = 0; j < b; j++) {"                                      +"\n"+
							"			*(ch1)=1;//DEFECT,NPD_EXP,ch1"                                     +"\n"+
							"		}"                                                                  +"\n"+
							"	}"                                                                   +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"NPD"
							,
				},
		});
	}
}
