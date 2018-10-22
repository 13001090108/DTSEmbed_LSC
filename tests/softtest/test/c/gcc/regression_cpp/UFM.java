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
public class UFM extends ModelTestBase {
	public UFM(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/UFM-0.1.xml";
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

				//////////////////////////0//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"void func(int* p, int a){"                                            +"\n"+
							"    a=*p;"                                                            +"\n"+
							"}"                                                                    +"\n"+
							"void test2(int b){"                                                   +"\n"+
							"	int *memleak_error1=NULL;"                                           +"\n"+
							"	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
							"	if (b > 0) {"                                                        +"\n"+
							"		free(memleak_error1);"                                              +"\n"+
							"	}"                                                                   +"\n"+
							"	func(memleak_error1, 1);//DEFECT, UFM, memleak_error1"               +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"UFM"
							,
				},
				
				//////////////////////////1//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"void test1(){"                                                        +"\n"+
							"	int *memleak_error1=NULL;"                                           +"\n"+
							"	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
							"	free(memleak_error1);"                                               +"\n"+
							"	*memleak_error1 = 1;//DEFECT, UFM, memleak_error1"                   +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"UFM"
							,
				},
				//////////////////////////2//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"void func(int* p, int a);"                                            +"\n"+
							"void test2(){"                                                        +"\n"+
							"	int *memleak_error1=NULL;"                                           +"\n"+
							"	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
							"	free(memleak_error1);"                                               +"\n"+
							"	func(memleak_error1, 1);//DEFECT, UFM, memleak_error1"               +"\n"+
							"}"                                                                    +"\n"+
							"void func(int * p,int a){"                                            +"\n"+
							"    *p;"                                                              +"\n"+
							"}"
							,
							"gcc"
							,
							"UFM"
							,
				},

				//////////////////////////3//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"int* test3(){"                                                        +"\n"+
							"	int *memleak_error1=NULL;"                                           +"\n"+
							"	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
							"	free(memleak_error1);"                                               +"\n"+
							"	return memleak_error1;//DEFECT, UFM, memleak_error1"                 +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"UFM"
							,
				},

				//////////////////////////4//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"int* test4(){"                                                        +"\n"+
							"	int *memleak_error1=NULL;"                                           +"\n"+
							"	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
							"	free(memleak_error1);"                                               +"\n"+
							"	memleak_error1[0] = 1;//DEFECT, UFM, memleak_error1"                 +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"UFM"
							,
				},

				//////////////////////////5////////////////////////////////////////	
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"int* test5(){"                                                        +"\n"+
							"	int *memleak_error1=NULL;"                                           +"\n"+
							"	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
							"	free(memleak_error1);"                                               +"\n"+
							"	int *p;"                                                             +"\n"+
							"	p = memleak_error1 + 1;//DEFECT, UFM, memleak_error1"                +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"UFM"
							,
				},

				//////////////////////////6//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"int* func1();"                                                        +"\n"+
							"void test1(){"                                                        +"\n"+
							"	int *memleak_error1=NULL;"                                           +"\n"+
							"	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
							"	free(memleak_error1);"                                               +"\n"+
							"	memleak_error1 = func1();"                                           +"\n"+
							"	*memleak_error1 = 1; // FP, UFM"                                     +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void func(int* p, int a);"                                            +"\n"+
							"void test2(){"                                                        +"\n"+
							"	int *memleak_error1=NULL;"                                           +"\n"+
							"	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
							"	free(memleak_error1);"                                               +"\n"+
							"	memleak_error1 = func1();"                                           +"\n"+
							"	func(memleak_error1, 1);// FP, UFM"                                  +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int* test3(){"                                                        +"\n"+
							"	int *memleak_error1=NULL;"                                           +"\n"+
							"	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
							"	free(memleak_error1);"                                               +"\n"+
							"	memleak_error1 = func1();"                                           +"\n"+
							"	return memleak_error1;// FP, UFM"                                    +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int* test4(){"                                                        +"\n"+
							"	int *memleak_error1=NULL;"                                           +"\n"+
							"	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
							"	free(memleak_error1);"                                               +"\n"+
							"	memleak_error1 = func1();"                                           +"\n"+
							"	memleak_error1[0] = 1;// FP, UFM"                                    +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int* test5(){"                                                        +"\n"+
							"	int *memleak_error1=NULL;"                                           +"\n"+
							"	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
							"	free(memleak_error1);"                                               +"\n"+
							"	memleak_error1 = func1();"                                           +"\n"+
							"	int *p;"                                                             +"\n"+
							"	p = memleak_error1 + 1;// FP, UFM"                                   +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},

				//////////////////////////7//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+	
							"void test1(int b){"                                                   +"\n"+
							"	int *memleak_error1=NULL;"                                           +"\n"+
							"	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
							"	if (b > 0) {"                                                        +"\n"+
							"		free(memleak_error1);"                                              +"\n"+
							"	}"                                                                   +"\n"+
							"	*memleak_error1 = 1;//DEFECT, UFM, memleak_error1"                   +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"UFM"
							,
				},

				//////////////////////////8//////////////////////////////////////////////	
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"void func(int* p, int a);"                                            +"\n"+
							"void test2(int b){"                                                   +"\n"+
							"	int *memleak_error1=NULL;"                                           +"\n"+
							"	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
							"	if (b > 0) {"                                                        +"\n"+
							"		free(memleak_error1);"                                              +"\n"+
							"	}"                                                                   +"\n"+
							"	func(memleak_error1, 1);//DEFECT, UFM, memleak_error1"               +"\n"+
							"}"                                                                    +"\n"+
							"void func(int * p,int a){"                                            +"\n"+
							"    *p;"                                                              +"\n"+
							"}" 
							,
							"gcc"
							,
							"UFM"
							,
				},

				//////////////////////////9//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"int* test3(int b){"                                                   +"\n"+
							"	int *memleak_error1=NULL;"                                           +"\n"+
							"	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
							"	if (b > 0) {"                                                        +"\n"+
							"		free(memleak_error1);"                                              +"\n"+
							"	}"                                                                   +"\n"+
							"	return memleak_error1;//DEFECT, UFM, memleak_error1"                 +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"UFM"
							,
				},

				//////////////////////////10//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"int* test4(int b){"                                                   +"\n"+
							"	int *memleak_error1=NULL;"                                           +"\n"+
							"	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
							"	if (b > 0) {"                                                        +"\n"+
							"		free(memleak_error1);"                                              +"\n"+
							"	}"                                                                   +"\n"+
							"	memleak_error1[0] = 1;//DEFECT, UFM, memleak_error1"                 +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"UFM"
							,
				},

				//////////////////////////11//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"int* test5(int b){"                                                   +"\n"+
							"	int *memleak_error1=NULL;"                                           +"\n"+
							"	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
							"	if (b > 0) {"                                                        +"\n"+
							"		free(memleak_error1);"                                              +"\n"+
							"	}"                                                                   +"\n"+
							"	int *p;"                                                             +"\n"+
							"	p = memleak_error1 + 1;//DEFECT, UFM, memleak_error1"                +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"UFM"
							,
				},
				//////////////////////////12//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"int* func1();"                                                        +"\n"+
							"void test1(int b){"                                                   +"\n"+
							"	int *memleak_error1=NULL;"                                           +"\n"+
							"	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
							"	if (b > 0) {"                                                        +"\n"+
							"		free(memleak_error1);"                                              +"\n"+
							"	}"                                                                   +"\n"+
							"	memleak_error1 = func1();"                                           +"\n"+
							"	*memleak_error1 = 1;//FP, UFM"                                       +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void func(int* p, int a);"                                            +"\n"+
							"void test2(int b){"                                                   +"\n"+
							"	int *memleak_error1=NULL;"                                           +"\n"+
							"	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
							"	if (b > 0) {"                                                        +"\n"+
							"		free(memleak_error1);"                                              +"\n"+
							"	}"                                                                   +"\n"+
							"	memleak_error1 = func1();"                                           +"\n"+
							"	func(memleak_error1, 1);//FP, UFM"                                   +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int* test3(int b){"                                                   +"\n"+
							"	int *memleak_error1=NULL;"                                           +"\n"+
							"	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
							"	if (b > 0) {"                                                        +"\n"+
							"		free(memleak_error1);"                                              +"\n"+
							"	}"                                                                   +"\n"+
							"	memleak_error1 = func1();"                                           +"\n"+
							"	return memleak_error1;//FP, UFM"                                     +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int* test4(int b){"                                                   +"\n"+
							"	int *memleak_error1=NULL;"                                           +"\n"+
							"	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
							"	if (b > 0) {"                                                        +"\n"+
							"		free(memleak_error1);"                                              +"\n"+
							"	}"                                                                   +"\n"+
							"	memleak_error1 = func1();"                                           +"\n"+
							"	memleak_error1[0] = 1;//FP, UFM"                                     +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int* test5(int b){"                                                   +"\n"+
							"	int *memleak_error1=NULL;"                                           +"\n"+
							"	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
							"	if (b > 0) {"                                                        +"\n"+
							"		free(memleak_error1);"                                              +"\n"+
							"	}"                                                                   +"\n"+
							"	memleak_error1 = func1();"                                           +"\n"+
							"	int *p;"                                                             +"\n"+
							"	p = memleak_error1 + 1;//FP, UFM"                                    +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},

				//////////////////////////13//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"int* func1();"                                                        +"\n"+
							"void test1(int b){"                                                   +"\n"+
							"	int *memleak_error1=NULL;"                                           +"\n"+
							"	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
							"	if (b > 0) {"                                                        +"\n"+
							"		free(memleak_error1);"                                              +"\n"+
							"		memleak_error1 = func1();"                                          +"\n"+
							"	}"                                                                   +"\n"+
							"	*memleak_error1 = 1;//FP, UFM"                                       +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void func(int* p, int a);"                                            +"\n"+
							"void test2(int b){"                                                   +"\n"+
							"	int *memleak_error1=NULL;"                                           +"\n"+
							"	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
							"	if (b > 0) {"                                                        +"\n"+
							"		free(memleak_error1);"                                              +"\n"+
							"		memleak_error1 = func1();"                                          +"\n"+
							"	}"                                                                   +"\n"+
							"	func(memleak_error1, 1);//FP, UFM"                                   +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int* test3(int b){"                                                   +"\n"+
							"	int *memleak_error1=NULL;"                                           +"\n"+
							"	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
							"	if (b > 0) {"                                                        +"\n"+
							"		free(memleak_error1);"                                              +"\n"+
							"		memleak_error1 = func1();"                                          +"\n"+
							"	}"                                                                   +"\n"+
							"	return memleak_error1;//FP, UFM"                                     +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int* test4(int b){"                                                   +"\n"+
							"	int *memleak_error1=NULL;"                                           +"\n"+
							"	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
							"	if (b > 0) {"                                                        +"\n"+
							"		free(memleak_error1);"                                              +"\n"+
							"		memleak_error1 = func1();"                                          +"\n"+
							"	}"                                                                   +"\n"+
							"	memleak_error1[0] = 1;//FP, UFM"                                     +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int* test5(int b){"                                                   +"\n"+
							"	int *memleak_error1=NULL;"                                           +"\n"+
							"	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
							"	if (b > 0) {"                                                        +"\n"+
							"		free(memleak_error1);"                                              +"\n"+
							"		memleak_error1 = func1();"                                          +"\n"+
							"	}"                                                                   +"\n"+
							"	int *p;"                                                             +"\n"+
							"	p = memleak_error1 + 1;//FP, UFM"                                    +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},

				//////////////////////////14//////////////////////////////////////////////
				//jdh  需要修改 xwt
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"void test1(int *memleak_error1){"                                     +"\n"+
							"	free(memleak_error1);"                                               +"\n"+
							"	*memleak_error1 = 1;//DEFECT, UFM, memleak_error1"                   +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"UFM"
							,
				},

				//////////////////////////15//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"void func(int* p, int a);"                                            +"\n"+
							"void test2(int *memleak_error1){"                                     +"\n"+
							"	free(memleak_error1);"                                               +"\n"+
							"	func(memleak_error1, 1);//DEFECT, UFM, memleak_error1"               +"\n"+
							"}"                                                                    +"\n"+
							"void func(int * p,int a){"                                            +"\n"+
							"    *p;"                                                              +"\n"+
							"}" 
							,
							"gcc"
							,
							"UFM"
							,
				},

				//////////////////////////16//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"int* test3(int* memleak_error1){"                                     +"\n"+
							"	free(memleak_error1);"                                               +"\n"+
							"	return memleak_error1;//DEFECT, UFM, memleak_error1"                 +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"UFM"
							,
				},

				//////////////////////////17//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"int* test4(int* memleak_error1){"                                     +"\n"+
							"	free(memleak_error1);"                                               +"\n"+
							"	memleak_error1[0] = 1;//DEFECT, UFM, memleak_error1"                 +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"UFM"
							,
				},

				//////////////////////////18//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"int* test5(int* memleak_error1){"                                     +"\n"+
							"	free(memleak_error1);"                                               +"\n"+
							"	int *p;"                                                             +"\n"+
							"	p = memleak_error1 + 1;//DEFECT, UFM, memleak_error1"                +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"UFM"
							,
				},
				
				//////////////////////////19//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+ 
							"  int *foo(int t) {"                                                  +"\n"+
							"      int *x = (int *)malloc(1);"                                     +"\n"+
							"      if (!t) {"                                                      +"\n"+
							"          free(x);"                                                   +"\n"+
							"      }"                                                              +"\n"+
							"      *x = t; //DEFECT"                                               +"\n"+
							"      return x;"                                                      +"\n"+
							" }"                                                                   
							,
							"gcc"
							,
							"UFM"
							,
				},

				//////////////////////////20//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"  int foo() {"                                                        +"\n"+
							"      int *x = (int *)malloc(4);"                                     +"\n"+
							"      *x = 10;"                                                       +"\n"+
							"      free(x);"                                                       +"\n"+
							"      return *x; //DEFECT"                                            +"\n"+
							"  }"                                                                  
							,
							"gcc"
							,
							"UFM"
							,
				},

				//////////////////////////21//////////////////////////////////////////////
				//xwt:没有识别重复释放的机制
				//jdh  需要修改 xwt

				{
					"  #include <stdlib.h>"                                                +"\n"+
							"  "                                                                   +"\n"+
							"  struct foo {"                                                       +"\n"+
							"      int s1;"                                                        +"\n"+
							"  };"                                                                 +"\n"+
							"  "                                                                   +"\n"+
							"  int free_freed(void) {"                                             +"\n"+
							"      int found;"                                                     +"\n"+
							"      int i;"                                                         +"\n"+
							"     struct foo *x;"                                                  +"\n"+
							"     x = (struct foo *) calloc(1, sizeof(struct foo));"               +"\n"+
							"     if (x == 0)"                                                     +"\n"+
							"        return 0;"                                                    +"\n"+
							"     found = rand();"                                                 +"\n"+
							"     if (found == 0) {"                                               +"\n"+
							"        i = x->s1;"                                                   +"\n"+
							"        free(x);"                                                     +"\n"+
							"     } else {"                                                        +"\n"+
							"        found = x->s1;"                                               +"\n"+
							"     }"                                                               +"\n"+
							"     free(x); //DEFECT"                                               +"\n"+
							"     return 0;"                                                       +"\n"+
							" }"                                                                   
							,
							"gcc"
							,
							"UFM"
							,
				},

				//////////////////////////22//////////////////////////////////////////////
				//xwt:没有识别重复释放的机制
				//jdh 同上
				{
					"  #include <stdlib.h>"                                                +"\n"+
							"  "                                                                   +"\n"+
							"  typedef struct x {"                                                 +"\n"+
							"      char * field;"                                                  +"\n"+
							"  } tx;"                                                              +"\n"+
							"  "                                                                   +"\n"+
							"  void release(tx * a){"                                              +"\n"+
							"      free(a->field);"                                                +"\n"+
							"      free(a);"                                                       +"\n"+
							" }"                                                                   +"\n"+
							" "                                                                    +"\n"+
							" int main() {"                                                        +"\n"+
							"     tx *a = (tx *)malloc(sizeof(tx));"                               +"\n"+
							"     if (a==0) return;"                                               +"\n"+
							"     a->field = (char *)malloc(10);"                                  +"\n"+
							"     release(a);"                                                     +"\n"+
							"     free(a->field); //DEFECT"                                        +"\n"+
							"     free(a);//DEFECT"                                                +"\n"+
							"    "                                                                 +"\n"+
							" }"                                                                   
							,
							"gcc"
							,
							"UFM"
							,
				},

				//////////////////////////23//////////////////////////////////////////////
				{
					" #include <stdlib.h>"                                                 +"\n"+
							"  "                                                                   +"\n"+
							"  int *foo(int t) {"                                                  +"\n"+
							"      static int *x = NULL;"                                          +"\n"+
							"      if (!x) {"                                                      +"\n"+
							"          x = (int *)malloc(sizeof(int));"                            +"\n"+
							"      }"                                                              +"\n"+
							"      if (t) {"                                                       +"\n"+
							"          free(x); "                                                  +"\n"+
							"     }"                                                               +"\n"+
							"     return x; //DEFECT"                                              +"\n"+
							" }"                                                                   
							,
							"gcc"
							,
							"UFM"
							,
				},

				//////////////////////////24//////////////////////////////////////////////
				{
					"  #include <stdlib.h>"                                                +"\n"+
							"  "                                                                   +"\n"+
							"  int *foo() {"                                                       +"\n"+
							"      int *x = (int *)malloc(sizeof(int));"                           +"\n"+
							"      free(x);"                                                       +"\n"+
							"      return x; //DEFECT"                                             +"\n"+
							"  }"                                                                  
							,
							"gcc"
							,
							"UFM"
							,
				},

				//////////////////////////25//////////////////////////////////////////////
				{
					"  #include <stdlib.h>"                                                +"\n"+
							"  "                                                                   +"\n"+
							"  int *foo(int t) {"                                                  +"\n"+
							"      static int *x = NULL;"                                          +"\n"+
							"      if (!x) {"                                                      +"\n"+
							"          x = (int *)malloc(4 * sizeof(int));"                        +"\n"+
							"      }"                                                              +"\n"+
							"      if (t) {"                                                       +"\n"+
							"          free(x);"                                                   +"\n"+
							"     }"                                                               +"\n"+
							"     return x + 1; //DEFECT"                                          +"\n"+
							" }"                                                                   
							,
							"gcc"
							,
							"UFM"
							,
				},

				//////////////////////////26//////////////////////////////////////////////
				{
					"  #include <stdlib.h>"                                                +"\n"+
							"  "                                                                   +"\n"+
							"  int *foo() {"                                                       +"\n"+
							"      int *x = (int *)malloc(4 * sizeof(int));"                       +"\n"+
							"      free(x);"                                                       +"\n"+
							"      return x + 1; //DEFECT"                                         +"\n"+
							"  }"                                                                  
							,
							"gcc"
							,
							"UFM"
							,
				},

				//////////////////////////27//////////////////////////////////////////////
				/*xwt:雷同于MLF中未通过用例，循环体在控制流图中只迭代了一遍，无法检测*/
				//jdh 考虑
				{
					"  #include <stdlib.h>"                                                +"\n"+
							"  #include <string.h> "                                               +"\n"+
							"  "                                                                   +"\n"+
							"  void foo(int flag) {"                                               +"\n"+
							"      char *x = (char*)malloc(10);"                                   +"\n"+
							"      int i=10;"                                                      +"\n"+
							"      for(i=0;i<10;i++){"                                             +"\n"+
							"          strcpy(x,\"qwdwq\"); //DEFECT"                                +"\n"+
							"          if(flag)"                                                   +"\n"+
							"             free(x);"                                                +"\n"+
							"      }"                                                              +"\n"+
							"  }"                                                                  
							,
							"gcc"
							,
							"OK"
							,
				},
//////////////////////////28//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
					"int* func1();"                                                        +"\n"+
					"void test1(){"                                                        +"\n"+
					"	int **memleak_error1=NULL;"                                           +"\n"+
					"	*memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
					"	free(*memleak_error1);"                                               +"\n"+
					"	*memleak_error1 = func1();"                                           +"\n"+
					"	*memleak_error1 = 1; // FP, UFM"                                     +"\n"+
					"}"                                                                 
					,
					"gcc"
					,
					"OK"
					,
				}

								
			
		});
	}
}
