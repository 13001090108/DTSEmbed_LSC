package softtest.test.c.gcc.expression;

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
public class NPD_EXP extends ModelTestBase {
	public NPD_EXP(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/NPD_EXP-0.1.xml";
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
	/////////////////  0   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <malloc.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "void npd_f1(){"                                                       +"\n"+
		            "    struct pb{"                                                       +"\n"+
		            "	   char *c;"                                                         +"\n"+
		            "	};"                                                                  +"\n"+
		            "	struct pc{"                                                          +"\n"+
		            "	   struct pb* B;"                                                    +"\n"+
		            "	}C;"                                                                 +"\n"+
		            "	C.B->c= NULL;"                                                       +"\n"+
		            "	*(C.B->c) = 'c'; //Defect,NPD_EXP,C.B->c"                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            ,
		            },
	/////////////////  1   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <malloc.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "void npd_f2(){"                                                       +"\n"+
		            "    struct pb{"                                                       +"\n"+
		            "	   char *c;"                                                         +"\n"+
		            "	}spb;"                                                                  +"\n"+
		            "	struct pc{"                                                          +"\n"+
		            "	   struct pb* B;"                                                    +"\n"+
		            "	}D;"                                                                 +"\n"+
		            "	char ch;"                                                            +"\n"+
		            "	D.B=&spb;"                                                            +"\n"+
		            "	D.B->c= &ch;"                                                        +"\n"+
		            "	*(D.B->c) = 'c'; //FP"                                               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  2   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <malloc.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "void npd_f3(){"                                                       +"\n"+
		            "	struct p{"                                                           +"\n"+
		            "	   int *i;"                                                          +"\n"+
		            "	}A;"                                                                 +"\n"+
		            "	A.i = (int *)malloc(4);"                                             +"\n"+
		            "	*(A.i) = 1; //Defect,NPD_EXP,A.i"                                    +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            ,
		            },
	/////////////////  3   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <malloc.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "int npd_f4(){"                                                        +"\n"+
		            "	struct p{"                                                           +"\n"+
		            "	   int *i;"                                                          +"\n"+
		            "	}A;"                                                                 +"\n"+
		            "	A.i = (int *)malloc(4);"                                             +"\n"+
		            "	if(A.i == NULL)"                                                     +"\n"+
		            "	   return 0;"                                                        +"\n"+
		            "	else"                                                                +"\n"+
		            "	   *(A.i) = 1;//FP"                                                  +"\n"+
		            "	return 1;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  4   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <malloc.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "int npd_f5(){"                                                        +"\n"+
		            "	struct p{"                                                           +"\n"+
		            "	   int *x;"                                                          +"\n"+
		            "       int **y;"                                                      +"\n"+
		            "	}A;"                                                                 +"\n"+
		            "	A.x = NULL;"                                                         +"\n"+
		            "    A.y = NULL;"                                                      +"\n"+
		            "    **(A.y) = 2;//Defect,NPD_EXP,A.y"                                             +"\n"+
		            "	return 1;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            ,
		            },
	/////////////////  5   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "#include <malloc.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "void npd_f7(){"                                                       +"\n"+
		            "	struct p{"                                                           +"\n"+
		            "	   int *i;"                                                          +"\n"+
		            "	}A;"                                                                 +"\n"+
		            "	A.i = (int *)malloc(4);"                                             +"\n"+
		            "	if(A.i != NULL && *(A.i) == 1)//FP,OK"                               +"\n"+
		            "	   *(A.i) = 2; //FP,OK"                                              +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  6   ///////////////////	
		            {
		            "#include  <stdio.h>"                                                  +"\n"+
		            "typedef  struct{"                                                     +"\n"+
		            "    char a[22];"                                                      +"\n"+
		            "    char* p;"                                                         +"\n"+
		            "}S;"                                                                  +"\n"+
		            "S  *s1,*s2;"                                                          +"\n"+
		            "void f(){"                                                            +"\n"+
		            "   s1->p=(char*)malloc(11);"                                          +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f1(){"                                                           +"\n"+
		            "   f();"                                                              +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2(){"                                                           +"\n"+
		            "   f1();"                                                             +"\n"+
		            "   *(s1->p)='a';"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            ,
		            },
	/////////////////  7   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "typedef struct{"                                                      +"\n"+
		            "  char* p;"                                                           +"\n"+
		            "}S;"                                                                  +"\n"+
		            "S *s;"                                                                +"\n"+
		            "void f(){"                                                            +"\n"+
		            "   s->p=0;"                                                           +"\n"+
		            "   *(s->p);"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            ,
		            },
/////////////////  8   ///////////////////
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_exp_2_f1()"                                               +"\n"+
		            "{"                                                                    +"\n"+
		            "	int *ptr;"                                                           +"\n"+
		            ""                                                                     +"\n"+
		            "	ptr = (int*)malloc(4 * sizeof(int));"                                +"\n"+
		            "	if (!ptr)"                                                           +"\n"+
		            "		return;"                                                            +"\n"+
		            "	*(ptr + 2) = 5; //FP"                                                +"\n"+
		            "	free(ptr);"                                                          +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
/////////////////  9   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "#include <string.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                  +"\n"+
		            "char *ghx_npd_4_f4(char *b)"                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "    int i, m, n;"                                                     +"\n"+
		            "    char *s;"                                                         +"\n"+
		            ""                                                                     +"\n"+
		            "    m = strlen(b);"                                                   +"\n"+
		            "    n = m;"                                                           +"\n"+
		            "    s = (char *) malloc(n + 1);"                                      +"\n"+
		            "    for (i = 0; i < m; i++)"                                          +"\n"+
		            "	{"                                                                   +"\n"+
		            "        *(s + i) = *(b + i);//DEFECT"                                 +"\n"+
		            "	}"                                                                   +"\n"+
		            "    *(s + m) = NULL;"                                                 +"\n"+
		            "    return (s);"                                                      +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            ,
		            },
/////////////////  10   ///////////////////
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "#include <string.h>"                                                  +"\n"+
		            "struct ghx_npd_5_s5"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	char* ss;"                                                           +"\n"+
		            ""                                                                     +"\n"+
		            "};"                                                                   +"\n"+
		            "void ghx_npd_5_f5()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	struct ghx_npd_5_s5 s;"                                              +"\n"+
		            "	s.ss=(char*)malloc(10);"                                             +"\n"+
		            "	char* a=(char*)malloc(10);"                                          +"\n"+
		            "	s.ss[0]=*a;//DEFECT"                                                 +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            ,
		            },
/*dongyk 2012 04 10后续的测试用例为测试表达式识别充分性补充的*/		            
/////////////////  11   ///////////////////
    //（1）指向普通指针的指针，指针引用形式形如：**p；		            
		            {
		            	"void dyk_npd_f1()()"                                                  +"\n"+
			            "{"                                                                    +"\n"+
			            "	int p;"                                              +"\n"+
			            "	int *p1=0;"                                            +"\n"+
			            "	int **p2;"                                          +"\n"+
			            "	p2=&p1;"                                           +"\n"+
			            "	*p2=0;"                                                 +"\n"+
			            "   p=**p2;    //指针表达式 *p2"                 +"\n"+   
			            "}"	            	
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            ,
		            },
/////////////////  12   ///////////////////
//（2）指向数组的指针，指针引用形式形如：(*str)[1]；	
		            {
		            	"void dyk_npd_f2()()"                                   +"\n"+
		            	"{"                                                  +"\n"+
		            	"	int p;"                                            +"\n"+
		            	"	int *p1;"                                            +"\n"+
		            	"	int **p2;"                                            +"\n"+
		            	"	int str[3]={90,91,92};"                                            +"\n"+
		            	"	p1=str;"                                            +"\n"+
		            	"	p2=&p1;"                                            +"\n"+
		            	"	*p2=&str;"                                            +"\n"+
		            	"	p=(*p2)[1];    //指针表达式 *p2"                                            +"\n"+
		            	"}" 
		            ,
				    "gcc"
				    ,
				    "OK"
				    ,	
		            },
/////////////////  13   ///////////////////
//(3)指向结构体指针的指针，指针引用形式形如：(*std)->name；	
		            {
		            	"typedef struct _st3 {"                                   +"\n"+
		            	"	int age;"                                   +"\n"+
		            	"}st3;"                                   +"\n"+
		            	"void f3()"                                   +"\n"+
		            	"{"                                   +"\n"+
		            	"	int age;"                                   +"\n"+
		            	"	st3 *p1st3;"                                   +"\n"+
		            	"	st3 **p2st3;"                                   +"\n"+
		            	"	p1st3->age=20;"                                   +"\n"+
		            	"	p2st3=&p1st3;"                                   +"\n"+
		            	"	*p2st3=0;"                                   +"\n"+
		            	"	age=(*p2st3)->age;    //指针表达式 *p2st3"                                   +"\n"+
		            	"}"
		            	,
					    "gcc"
					    ,
					    "NPD_EXP"
					    ,	
		            },
/////////////////  14   ///////////////////		               
////（4）指向函数指针的指针，指针引用形式形如：(**ptr)(a,b)；		               
		            {
		            	"int max4(int x,int y)"                                   +"\n"+
		            	"{"                                   +"\n"+
		            	"	return(x>y?x:y);"                                   +"\n"+
		            	"}"                                   +"\n"+
		            	"void f4()"                                   +"\n"+
		            	"{"                                   +"\n"+
		            	"	int (*ptr1)(int, int);"                                   +"\n"+
		            	"	int (**ptr2)(int, int);"                                   +"\n"+
		            	"	int a=10;"                                   +"\n"+
		            	"	int b=20;"                                   +"\n"+
		            	"	ptr1=max4;"                                   +"\n"+
		            	"	ptr2=&ptr1;"                                   +"\n"+
		            	"	*ptr2=max4;"                                   +"\n"+
		            	"	a=(**ptr2)(a,b);    //指针表达式 *ptr2"                                   +"\n"+
		            	"}"
		            	,
					    "gcc"
					    ,
					    "OK"
					    ,	
		            },		               
/////////////////  15   ///////////////////		               
//////（5）指针数组，指针引用形式形如：*str[1]；		                            
		            {
		            	"void f5()"                                   +"\n"+
		            	"{"                                   +"\n"+
		            	"	int a=10;"                                   +"\n"+
		            	"	int *p1=&a;"                                   +"\n"+
		            	"	int* arr[2];"                                   +"\n"+
		            	"	int b;"                                   +"\n"+
		            	"	arr[1]=0;"                                   +"\n"+		            	
		            	"	b=*arr[1];    //指针表达式 arr[1]"                                   +"\n"+
		            	"}"
		            	,
					    "gcc"
					    ,
					    "NPD_EXP"
					    ,	
		            },		               
/////////////////  16   ///////////////////		               
//////6）二维数组，指针引用形式形如：str[2][3]；  有问题：未识别出a[1]		            
		            {
		            	"void f6()"                                   +"\n"+
		            	"{"                                   +"\n"+
		            	"	int a[2][2]={1,2,3,4};"                                   +"\n"+
		            	"	int b=a[1][1];   //指针表达式 a[1]"                                   +"\n"+
		            	"}"
		            	,
					    "gcc"
					    ,
					    "OK"
					    ,	
		            },		            	               
/////////////////  17   ///////////////////		               
//////（7）结构体数组，指针引用形式形如：str[1]->name；
		            {
		            	"typedef struct _st7 {"                                   +"\n"+
		            	"	int age;"                                   +"\n"+
		            	"}st7;"                                   +"\n"+
		            	"void f7()"                                   +"\n"+
		            	"{"                                   +"\n"+
		            	"   int iage;"                                   +"\n"+
		            	"   st7 p1st7={20};"                                   +"\n"+
		            	"	st7 *p2st7;"                                   +"\n"+
		            	"	p2st7=&p1st7;"                                   +"\n"+
		            	"	st7* st7arr[2];"                                   +"\n"+
		            	"	st7arr[1]=0;"                                   +"\n"+		            	
		            	"	iage=st7arr[1]->age;   //指针表达式 a[1]"                                   +"\n"+
		            	""                                   +"\n"+
		            	"}"
		            	,
					    "gcc"
					    ,
					    "NPD_EXP"
					    ,	
		            },
/////////////////  18   ///////////////////		               
//////(8)函数指针数组，指针引用形式形如：*op[0](2,3)；			            
		            {
		            	"int max8(int x,int y)"                                   +"\n"+
		            	"{"                                   +"\n"+
		            	"	return(x>y?x:y);"                                   +"\n"+
		            	"}"                                   +"\n"+
		            	"void f8()"                                   +"\n"+
		            	"{"                                   +"\n"+
		            	"	int (*ptr1)(int, int)=max8;"                                   +"\n"+
		            	"	int (*ptr2[2])(int, int);"                                   +"\n"+
		            	"	ptr2[1]=ptr1;"                                   +"\n"+
		            	"	int a=(*ptr2[1])(3,4);   //指针表达式 ptr2[1]"                                   +"\n"+
		            	"}"
		            	,
					    "gcc"
					    ,
					    "OK"
					    ,	
		            },        
/////////////////  19   ///////////////////		               
//////(9)结构体指针，结构成员是指针，指针引用形式形如：*(std->name)；		            
		            {
		            	"typedef struct _st9 {"                                   +"\n"+
		            	"	int* age;"                                   +"\n"+
		            	"}st9;"                                   +"\n"+
		            	"void f9()"                                   +"\n"+
		            	"{"                                   +"\n"+
		            	"	int *myage=0;"                                   +"\n"+
		            	"	st9 myst9;"                                   +"\n"+
		            	"	st9 *pst9=&myst9;"                                   +"\n"+
		            	"	pst9->age=myage;"                                   +"\n"+
		            	"	int iage=*(pst9->age);   //指针表达式 pst9->age"                                   +"\n"+
		            	"}"
		            	,
					    "gcc"
					    ,
					    "NPD_EXP"
					    ,	
		            },	            
/////////////////  20   ///////////////////		               
//////(10)结构体指针，结构成员是数组，指针引用形式形如：std->name[2]；
		            {
		            	"typedef struct _st10 {"                                   +"\n"+
		            	"	int age[3];"                                   +"\n"+
		            	"}st10;"                                   +"\n"+
		            	"void f10()"                                   +"\n"+
		            	"{"                                   +"\n"+
		            	"	int iage;"                                   +"\n"+
		            	"	st10  qst10;"                                   +"\n"+
		            	"	st10 *pst10;"                                   +"\n"+
		            	"	pst10=&qst10;"                                   +"\n"+
		            	"	pst10->age={1,2,3};"                                   +"\n"+
		            	"	iage=pst10->age[1];   //指针表达式 pst10->age"                                   +"\n"+
		            	"}"
		            	,
					    "gcc"
					    ,
					    "OK"
					    ,	
		            },
/////////////////  21   ///////////////////		               
//////(11)结构体指针，结构成员是结构体，指针引用形式形如：std->std1->name；		            
		            {
		            	"typedef struct _st11{"                                   +"\n"+
		            	"	int age;"                                   +"\n"+
		            	"	struct _st11 * st11;"                                   +"\n"+
		            	"}st11;"                                   +"\n"+
		            	"void f11()"                                   +"\n"+
		            	"{"                                   +"\n"+
		            	"	st11 qst11_1;"                                   +"\n"+
		            	"	st11 qst11_2;"                                   +"\n"+
		            	"	st11 *pst11;"                                   +"\n"+
		            	"	pst11=&qst11_1;"                                   +"\n"+
		            	"	pst11->st11=&qst11_2;"                                   +"\n"+
		            	"	pst11->st11->st11=0;"                                   +"\n"+
		            	"	int age=pst11->st11->st11->age;   //指针表达式 pst11->st11->st11"                                   +"\n"+
		            	"}"
		            	,
					    "gcc"
					    ,
					    "NPD_EXP"
					    ,	
		            },	            
/////////////////  22   ///////////////////		               
//////(12)结构体指针，结构成员是函数指针，指针引用形式形如：(*(std->ptr))(a,b)；			                    
		            {
		            	"int max12(int x,int y)"                                   +"\n"+
		            	"{"                                   +"\n"+ 
		            	"	return(x>y?x:y);"                                   +"\n"+
		            	"}"                                   +"\n"+ 
		            	"typedef struct _st12 {"                                   +"\n"+
		            	"	int (*ptr)(int, int);"                                   +"\n"+ 
		            	"}st12;"                                   +"\n"+
		            	"void f12()"                                   +"\n"+ 
		            	"{"                                   +"\n"+
		            	"	st12 qst12;"                                   +"\n"+ 
		            	"	st12 *pst12;"                                   +"\n"+
		            	"	pst12=&qst12;"                                   +"\n"+ 
		            	"	pst12->ptr=max12;"                                   +"\n"+ 
		            	"	int a=(*(pst12->ptr))(2,4);   //指针表达式 pst12->ptr"                                   +"\n"+ 
		            	"}"
		            	,
					    "gcc"
					    ,
					    "OK"
					    ,	
		            },
/////////////////  23   ///////////////////		               
//////(13)函数指针指向普通指针，指针引用形式形如：* (*ptr)(a,b)；				            
		            {
		            	"int * max13(a,b)"                                   +"\n"+
		            	"{"                                   +"\n"+
		            	"	a=a>b?a:b;"                                   +"\n"+
		            	"	return &a;"                                   +"\n"+
		            	"}"                                   +"\n"+
		            	"void f13()"                                   +"\n"+
		            	"{"                                   +"\n"+
		            	"	int *(*ptr)(int, int);"                                   +"\n"+
		            	"	ptr=max13;"                                   +"\n"+
		            	"	int a=*(*ptr)(2,4);   //指针表达式*ptr"                                   +"\n"+
		            	""                                   +"\n"+
		            	"}"
		            	,
					    "gcc"
					    ,
					    "OK"
					    ,	
		            },
/////////////////  24   ///////////////////		               
//////(14)函数指针指向数组，指针引用形式形如： (*ptr)(a,b)[1]；		           
		            {
		            	"int *p;"                                   +"\n"+
		            	"int * max14(a)"                                   +"\n"+
		            	"{"                                   +"\n"+
		            	"	int arr[2];"                                   +"\n"+
		            	"	arr[0]=a;"                                   +"\n"+
		            	"	arr[1]=a+1;"                                   +"\n"+
		            	"	p=arr;"                                   +"\n"+
		            	"	return p;"                                   +"\n"+
		            	"}"                                   +"\n"+
		            	"int main()"                                   +"\n"+
		            	"{"                                   +"\n"+
		            	"	int *(*ptr14)(int);"                                   +"\n"+
		            	"	int b=20;"                                   +"\n"+
		            	"	ptr14=max14;"                                   +"\n"+
		            	"	b=(*ptr14)(b)[1];   //指针表达式*ptr14"                                   +"\n"+
		            	"}"
		            	,
					    "gcc"
					    ,
					    "OK"
					    ,	
		            },
/////////////////  25   ///////////////////		               
//////(15)函数指针指向结构体，指针引用形式形如：(*ptr)(2,3)->name；
		            {
		            	"typedef struct _st15 {"                                   +"\n"+
		            	"	int age;"                                   +"\n"+
		            	"}st15;"                                   +"\n"+
		            	"st15 * max15(a)"                                   +"\n"+
		            	"{"                                   +"\n"+
		            	"	st15 qst15={a+1};"                                   +"\n"+
		            	"	st15 *pst15=&qst15;"                                   +"\n"+
		            	"	return pst15;"                                   +"\n"+
		            	"}"                                   +"\n"+
		            	"void f15()"                                   +"\n"+
		            	"{"                                   +"\n"+
		            	"	st15 *(*ptr15)(int);"                                   +"\n"+
		            	"	int b=20;"                                   +"\n"+
		            	"	ptr15=max15;"                                   +"\n"+
		            	"	b=(*ptr15)(b)->age;   //指针表达式*ptr15"                                   +"\n"+
		            	"}"
		            	,
					    "gcc"
					    ,
					    "OK"
					    ,	
		            },		            		          
/////////////////  26   ///////////////////		               
//////(16)函数指针指向函数指针，指针引用形式形如：(*(*ptr)(2))(3)。
		            {
		            	"int max16(a,b)"                                   +"\n"+
		            	"{"                                   +"\n"+
		            	"	return a>b?a:b;"                                   +"\n"+
		            	"}"                                   +"\n"+
		            	"int (*f16_1(int a,int b))(int c,int d)"                                   +"\n"+
		            	"{"                                   +"\n"+
		            	"	return max16;"                                   +"\n"+
		            	"}"                                   +"\n"+
		            	"void f16()"                                   +"\n"+
		            	"{"                                   +"\n"+
		            	"	int a;"                                   +"\n"+
		            	"	int (*(*ptr16)(int,int))(int,int);"                                   +"\n"+
		            	"	ptr16=f16_1;"                                   +"\n"+
		            	"	a=(*(*ptr16)(2,3))(3,4);   //指针表达式*ptr16"                                   +"\n"+
		            	"}"
		            	,
					    "gcc"
					    ,
					    "OK"
					    ,	
		            },
		            
		            
/////////////////  27   ///////////////////		               
//////(27)结构体成员为简单指针的引用，语法形式*(st.a)	
		            {
		            	"struct st {"                                   +"\n"+
		            	"	int * a;"                                   +"\n"+
		            	"};"                                   +"\n"+
		            	"void fun()"                                   +"\n"+
		            	"{"                                   +"\n"+
		            	"	struct st pst;"                                   +"\n"+
		            	"	int b=10;"                                   +"\n"+
		            	"	pst.a=&b;"                                   +"\n"+
		            	"	b= *(pst.a)+2;   //指针表达式pst.a"                                   +"\n"+
		            	"}"
		            	,
					    "gcc"
					    ,
					    "OK"
					    ,	
		            },
/////////////////  28   ///////////////////		               
//////(28)结构体成员是数组，语法形式st.str[0]；	
		            {
			            "#include <stdlib.h>"                                                  +"\n"+
		            	"struct st {"                                   +"\n"+
		            	"	char * str;"                                   +"\n"+
		            	"};"                                   +"\n"+
		            	"void fun()"                                   +"\n"+
		            	"{"                                   +"\n"+
		            	"	struct st pst;"                                   +"\n"+
		            	"	pst.str=(char*)malloc(4);"                                   +"\n"+
		            	"	pst.str[0] = 'c';"                                   +"\n"+
		            	"	char c= pst.str[0];   //指针表达式pst.str"                                   +"\n"+
		            	"}"
		            	,
					    "gcc"
					    ,
					    "NPD_EXP"
					    ,	
		            },
/////////////////  29   ///////////////////		               
//////(29)带有指针算术的基本数据类型指针，形如*(p+2)	
		            {
		            	"void fun28()"                                   +"\n"+
		            	"{"                                   +"\n"+
		            	"	int i;"                                   +"\n"+
		            	"	int a[5]={0,1,2,3,4};"                                   +"\n"+
		            	"	int * p;"                                   +"\n"+
		            	"	p=a;"                                   +"\n"+
		            	"	i=*(p+2);   //指针表达式p+2"                                   +"\n"+
		            	"}"
		            	,
					    "gcc"
					    ,
					    "OK"
					    ,	
		            },		            
/////////////////  30   ///////////////////		               
//////(30)带有指针算术的数组变量，形如(a+1)[1]		            
		            {
		            	"void fun29()"                                   +"\n"+
		            	"{"                                   +"\n"+
		            	"	int  a[3];"                                   +"\n"+
		            	"	int b;"                                   +"\n"+
		            	"	b=(a+1)[1];   //指针表达式a+1"                                   +"\n"+
		            	"}"
		            	,
					    "gcc"
					    ,
					    "OK"
					    ,	
		            },
/////////////////  31   ///////////////////		               
//////(31)带有指针算术的结构体指针，形如(pst+1)->str		            
		            {
			            "#include <stdlib.h>"                                                  +"\n"+
		            	"typedef struct _st1 {"                                   +"\n"+
		            	"	char str;"                                   +"\n"+
		            	"}st1;"                                   +"\n"+
		            	"void fun30()"                                   +"\n"+
		            	"{"                                   +"\n"+
		            	"	st1* pst;"                                   +"\n"+
		            	"	pst = (st1*)malloc(sizeof(st1)*2);"                                   +"\n"+
		            	"	(pst+1)->str = 'c';  //指针表达式：pst+1"                                   +"\n"+
		            	"	free(pst);"                                   +"\n"+
		            	"}"
		            	,
					    "gcc"
					    ,
					    "NPD_EXP"
					    ,	
		            },
/////////////////  32   ///////////////////		               
//////(32)带有指针算术的函数指针，形如(pst+1)->str		            
		            {
		            	
			            "#include <stdlib.h>"                                                  +"\n"+
			            "int* fun31(){"                                   +"\n"+
		            	"	return (int*)malloc(sizeof(int)*5);"                                   +"\n"+
		            	"}"                                   +"\n"+
		            	"void fun31_1()"                                   +"\n"+
		            	"{"                                   +"\n"+
		            	"	int a;"                                   +"\n"+
		            	"	int *(*ptr)();"                                   +"\n"+
		            	"	ptr=fun31;  "                                   +"\n"+
		            	"	a=*(ptr()+1);//指针表达式：ptr()+1"                                   +"\n"+
		            	"}"
		            	,
					    "gcc"
					    ,
					    "NPD_EXP"
					    ,	
		            },	
/////////////////  33   ///////////////////		               
//////(33)指针数组，有数组下标是非常数的计算影响数组元素	
		            {
		            	
			            "void f33(int flag)"                                                  +"\n"+
			            "{"                                                  +"\n"+
			            "	int a=1;"                                                  +"\n"+
			            "	int *p1=&a;"                                                  +"\n"+
			            "	int* arr[2];"                                                  +"\n"+
			            "	arr[0]=p1;"                                                  +"\n"+
			            "	if(flag>0)"                                                  +"\n"+
			            "		arr[a-1]=0;"                                                  +"\n"+
			            "	a=*arr[0];"                                                  +"\n"+
		            	"}"
		            	,
					    "gcc"
					    ,
					    "NPD_EXP"
					    ,	
		            },
/////////////////  34   ///////////////////		               
//////(34)指针数组，数组下标是非常数的数组元素的解引用
		            {
		            	
			            "void f34(int flag)"                                                  +"\n"+
			            "{"                                                  +"\n"+
			            "	int a=0,b=1;"                                                  +"\n"+
			            "	int *p1=&a;"                                                  +"\n"+
			            "	int* arr[2];"                                                  +"\n"+
			            "	arr[0]=p1;"                                                  +"\n"+
			            "	arr[1]=0;"                                                  +"\n"+
			            "	if(flag>0)"                                                  +"\n"+
			            "		a++;"                                                  +"\n"+
			            "	b=*arr[a*2-1];"                                                  +"\n"+
		            	"}"
		            	,
					    "gcc"
					    ,
					    "NPD_EXP"
					    ,	
		            },
/////////////////  35   ///////////////////		               
//////(35)指针数组，数组下标是函数返回值		
		            {
			            "int getNum35()"                                                  +"\n"+
			            "{"                                                  +"\n"+
			            "	return 0;"                                                  +"\n"+
		            	"}"                                               +"\n"+
			            "void f35()"                                                  +"\n"+
			            "{"                                                  +"\n"+
			            "	int a=0,b=1;"                                                  +"\n"+
			            "	int *p1=&a;"                                                  +"\n"+
			            "	int* arr[2];"                                                  +"\n"+
			            "	arr[0]=p1;"                                                  +"\n"+
			            "	arr[1]=0;"                                                  +"\n"+
			            "	b=*arr[getNum35()];"                                                  +"\n"+
		            	"}"
		            	,
					    "gcc"
					    ,
					    "OK"
					    ,	
		            },
/////////////////  36   ///////////////////		               
//////(36)指针数组，数组下标是函数返回值		            
		            {
			            "int getNum36()"                                                  +"\n"+
			            "{"                                                  +"\n"+
			            "	return 1;"                                                  +"\n"+
		            	"}"                                               +"\n"+
			            "void f36()"                                                  +"\n"+
			            "{"                                                  +"\n"+
			            "	int a=0,b=1;"                                                  +"\n"+
			            "	int *p1=&a;"                                                  +"\n"+
			            "	int* arr[2];"                                                  +"\n"+
			            "	arr[0]=p1;"                                                  +"\n"+
			            "	arr[1]=0;"                                                  +"\n"+
			            "	b=*arr[getNum36()];"                                                  +"\n"+
		            	"}"
		            	,
					    "gcc"
					    ,
					    "NPD_EXP"
					    ,	
		            },
/////////////////  37   ///////////////////		               
//////(37)指针数组，数组下标是函数返回值	
		            {
			            "int getNum37(int flag)"                                                  +"\n"+
			            "{"                                                  +"\n"+
			            "	if(flag<0)"                                                  +"\n"+
			            "		return 0;"                                                  +"\n"+
			            "	else"                                                  +"\n"+
			            "		return 1;"                                                  +"\n"+
		            	"}"                                               +"\n"+
			            "void f37(int flag)"                                                  +"\n"+
			            "{"                                                  +"\n"+
			            "	int a=0,b=1;"                                                  +"\n"+
			            "	int *p1=&a;"                                                  +"\n"+
			            "	int* arr[2];"                                                  +"\n"+
			            "	arr[0]=p1;"                                                  +"\n"+
			            "	arr[1]=0;"                                                  +"\n"+
			            "	b=*arr[getNum37(flag)];"                                                  +"\n"+
		            	"}"
		            	,
					    "gcc"
					    ,
					    "NPD_EXP"
					    ,	
		            },
/////////////////  38   ///////////////////		               
//////(38)表达式中既有数组，也有结构体		            
		            {
			            "typedef struct _st38 {"                                                  +"\n"+
			            "	int a[3];"                                                  +"\n"+
			            "}st7;"                                                  +"\n"+
			            "void f38()"                                                  +"\n"+
			            "{"                                                  +"\n"+
			            "	int i=0;"                                                  +"\n"+
			            "	st7 q1st7;"                                                  +"\n"+
			            "	st7 *p1st7;"                                                  +"\n"+
			            "	q1st7.a[0]=1;"                                                  +"\n"+
			            "	q1st7.a[1]=2;"                                                  +"\n"+
			            "	q1st7.a[2]=3;"                                                  +"\n"+
			            "	p1st7=&q1st7;"                                                  +"\n"+
			            "	st7* st7arr[2];"                                                  +"\n"+
			            "	st7arr[0]=p1st7;"                                                  +"\n"+
			            "	st7arr[1]=0;"                                                  +"\n"+
			            "	i=st7arr[i+1]->a[1];"                                                  +"\n"+
		            	"}"
		            	,
					    "gcc"
					    ,
					    "NPD_EXP"
					    ,	
		            },
//////////////////////////39//////////////////////////////////////////////	
//////(39)表达式为函数指针
		            {
						"#include <stdlib.h>"                                                  +"\n"+															
							""                                                                     +"\n"+
							"char* m;"                                                             +"\n"+
							"char* func39(){"                                                     +"\n"+
							"    char * p = 0;"                                                    +"\n"+
							"    if( m != 0 ) {"                                                   +"\n"+
							"        int cOffset = 3;"                                             +"\n"+
							"        p = m + 3;"                                                   +"\n"+
							"    }"                                                                +"\n"+
							"    return p;"                                                        +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void test39() "                                                      +"\n"+
							"{"                                                                    +"\n"+
							"	char c =*func39();//DEFECT, NPD_EXP,func39"                        +"\n"+
							"}"
							,
							"gcc"
							,
							"NPD_EXP"
							,
					},
					
	/////////////////  40 dyk   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "void f40()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "char p1='a';"                                                         +"\n"+
		            "   char * p2;"                                                        +"\n"+
		            "   char ** p3;     "                                                  +"\n"+
		            "   p3=&p2;"                                                           +"\n"+
		            "   *p3=NULL;"                                                         +"\n"+
		            "   p1=**p3;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            ,
		            },
	/////////////////  41   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "void f41(){  "                                                       +"\n"+
		            "int* a[2];"                                                           +"\n"+
		            "a[1]=NULL;"                                                           +"\n"+
		            "int b;"                                                           +"\n"+
		            "b=a[1][1];                                    "                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            ,
		            },
	/////////////////  42   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "void f42(){  "                                                       +"\n"+
		            "    int *a[2];"                                                     +"\n"+
		            "    int b;"                                                           +"\n"+
		            "    a[1]=NULL;"                                                       +"\n"+
		            "    b=*a[1];                                    "                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            ,
		            },
	/////////////////  43   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "struct st43 {"                                                          +"\n"+
		            "	  int * a;"                                                          +"\n"+
		            "};							"                                                            +"\n"+
		            "void f43()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "	 struct st43 pst;"                                                    +"\n"+
		            "    int b;"                                                           +"\n"+
		            "    pst.a=NULL;"                                                      +"\n"+
		            "	 b= *(pst.a)+2;"                                                    +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            ,
		            },
	/////////////////  44   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "struct st44 {"                                                          +"\n"+
		            "	  char * str;"                                                       +"\n"+
		            "};						"                                                             +"\n"+
		            "void f44()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "	  struct st44 pst;"                                                    +"\n"+
		            "	  pst.str=(char*)malloc(13);"                                        +"\n"+
		            "	  pst.str[0] = 'c';"                                                 +"\n"+
		            "	  char c= pst.str[0];"                                               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            },
	/////////////////  45   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "struct st45 {"                                                          +"\n"+
		            "	  char * str;"                                                       +"\n"+
		            "};					"                                                              +"\n"+
		            "void f45()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "	  struct st45 sst;"                                                    +"\n"+
		            "     struct st45 * pst;"                                               +"\n"+
		            "     pst=&sst;"                                                      +"\n"+
		            "	  pst->str=(char*)malloc(13);"                                       +"\n"+
		            "	  pst->str[0] = 'c';"                                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            },
	/////////////////  46   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "typedef struct _st1 {                                            "    +"\n"+
		            "	  int a;                                                              "+"\n"+
		            "}st1;                                                               " +"\n"+
		            "typedef struct _st2 {                                              "  +"\n"+
		            "	  st1 * pst;                                                        "+"\n"+
		            "}st2;                                                                                                                               "+"\n"+
		            "void f46()                                                     "      +"\n"+
		            "{                                                                  "  +"\n"+
		            "	  st2 s;                                                            "+"\n"+
		            "	  s.pst=(st1*)malloc(sizeof(st1)*2);                              "  +"\n"+
		            "	  s.pst->a=1;                              "                         +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            },
	/////////////////  47   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "typedef struct{                                            "    +"\n"+
		            "	  int a;                                                              "+"\n"+
		            "}st1;                                                               " +"\n"+
		            "typedef struct{                                              "  +"\n"+
		            "	  st1  pst;                                                        " +"\n"+
		            "}st2;                                                                                                                               "+"\n"+
		            "void f47()                                                     "      +"\n"+
		            "{                                                                  "  +"\n"+
		            "	  st2 * s; "                                                         +"\n"+
		            "     s=(st2*)malloc(sizeof(st2)*2);   "                               +"\n"+
		            "     (s->pst).a=1;                           "                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            },
	/////////////////  48   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "typedef struct {                                         "            +"\n"+
		            "	  int a;                                                           " +"\n"+
		            "}st1;                                                            "    +"\n"+
		            "typedef struct {                                             "        +"\n"+
		            "	  st1* pst;                                                       "  +"\n"+
		            "	  char* str;                                                       " +"\n"+
		            "}st2;                                                                                                                              "+"\n"+
		            "void f48()                                            "               +"\n"+
		            "{                                                                 "   +"\n"+
		            "	  st2 sst2;"                                                         +"\n"+
		            "     st2* pst1;"                                                     +"\n"+
		            "     pst1=&sst2;"                                                    +"\n"+
		            "     pst1->pst=(st2*)malloc(sizeof(st2)*2);                          "+"\n"+
		            "	  pst1->pst->a = 1;                      "                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            },
	/////////////////  49   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "int* f49_1(){                                                       "   +"\n"+
		            "	  return (int*)malloc(sizeof(int)*5);                            "   +"\n"+
		            "}                                                                 "   +"\n"+
		            "void f49(){                                               "          +"\n"+
		            "	  f49_1()[0]=1;                                             "          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            },
	/////////////////  50   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "typedef struct {                                                      "+"\n"+
		            "	  char a[5];                                              "          +"\n"+
		            "} str; "                                                              +"\n"+
		            "str* f50_1(){                                                       "   +"\n"+
		            "	  return (str*)malloc(sizeof(str));                            "     +"\n"+
		            "}                                                                 "   +"\n"+
		            "void f50(){                                               "          +"\n"+
		            "	  f50_1()->a='1';                                             "        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            },
	/////////////////  51   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "typedef struct{                                                      "+"\n"+
		            "	  char *s;                                                "          +"\n"+
		            "} str;   "                                                            +"\n"+
		            "str* f51_1(){                                                       "   +"\n"+
		            "	  return (str*)malloc(sizeof(str)*5);                            "   +"\n"+
		            "}                                                                 "   +"\n"+
		            "void fun1(str **p){     "                                             +"\n"+
		            "	  f51_1()->s[0]='0';                                              "    +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            },
	/////////////////  52   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "int * mlc(int n)"                                                     +"\n"+
		            "{ "                                                                   +"\n"+
		            "    return (int*)malloc(n); "                                         +"\n"+
		            "}"                                                                    +"\n"+
		            "int f52()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "    int a;"                                                           +"\n"+
		            "    int *(*ptr)(int, int);"                                               +"\n"+
		            "    ptr=mlc;"                                                         +"\n"+
		            "    a=*(*ptr)(5);"                                                    +"\n"+
		            "    return 0;"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            },
	/////////////////  53   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "void f53()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "  int i;"                                                             +"\n"+
		            "  int * p;"                                                           +"\n"+
		            "  p=(int*)malloc(n);"                                                 +"\n"+
		            "  i=*(p+2);"                                                       +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            },
	/////////////////  54   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "void f54(){                                               "          +"\n"+
		            "    int  a;"                                                              +"\n"+
		            "    int * p;"                                                             +"\n"+
		            "    p=(int*)malloc(n);"                                               +"\n"+
		            "    a=(p+1)[1];                                     "                 +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            },
	/////////////////  55   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "typedef struct {"                                                     +"\n"+
		            "	char str;"                                                           +"\n"+
		            "}st1;							"                                                         +"\n"+
		            "void f55()"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "	st1* pst;"                                                           +"\n"+
		            "	pst = (st1*)malloc(sizeof(st1)*2);"                                  +"\n"+
		            "	(pst+1)->str = 'c';"                                                 +"\n"+
		            "	free(pst);"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            },
	/////////////////  56   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "int* f_56(){                                                       "   +"\n"+
		            "      return (int*)malloc(sizeof(int)*5);                         "   +"\n"+
		            "}                                                                 "   +"\n"+
		            "void f56(){  "                                                       +"\n"+
		            "     int a;"                                                          +"\n"+
		            "     a=*(f_56()+1);                                  "                 +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD_EXP"
		            }















		            
		            
		            
		            
		            
		 });
	 }
}
