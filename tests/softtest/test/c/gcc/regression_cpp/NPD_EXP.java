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
				
				//////////////////////////0//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"#include <string.h>"                                                  +"\n"+
							"#include <stdio.h>"                                                   +"\n"+
							""                                                                     +"\n"+
							"char* m;"                                                             +"\n"+
							"char* func1_2(){"                                                     +"\n"+
							"    char * p = 0;"                                                    +"\n"+
							"    if( m != 0 ) {"                                                   +"\n"+
							"        int cOffset = 3;"                                             +"\n"+
							"        p = m + 3;"                                                   +"\n"+
							"    }"                                                                +"\n"+
							"    return p;"                                                        +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void test3_1() "                                                      +"\n"+
							"{"                                                                    +"\n"+
							"	char c =*func1_2();//DEFECT, NPD_EXP,func1_2"                        +"\n"+
							"}"
							,
							"gcc"
							,
							"NPD_EXP"
							,
				},
				
				//////////////////////////1//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"#include <string.h>"                                                  +"\n"+
							"#include <stdio.h>"                                                   +"\n"+
							""                                                                     +"\n"+
							"void test5_1()"                                                       +"\n"+
							"{"                                                                    +"\n"+
							"	char* p;"                                                            +"\n"+
							"	p = (char*)malloc(sizeof(char)*2);"                                  +"\n"+
							"	*(p+1) = 1;//DEFECT, NPD_EXP,p+1"                                    +"\n"+
							"	free(p);"                                                            +"\n"+
							"}"
							,
							"gcc"
							,
							"NPD_EXP"
							,
				},
				//////////////////////////2//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"#include <string.h>"                                                  +"\n"+
							"#include <stdio.h>"                                                   +"\n"+
							""                                                                     +"\n"+
							"void test6_1(int i)"                                                  +"\n"+
							"{"                                                                    +"\n"+
							"	char* p;"                                                            +"\n"+
							"	p = (char*)malloc(sizeof(char)*i);"                                  +"\n"+
							"	*(p+i) = 1;//DEFECT, NPD_EXP,p+i"                                    +"\n"+
							"	free(p);"                                                            +"\n"+
							"}"
							,
							"gcc"
							,
							"NPD_EXP"
							,
				},
				//////////////////////////3//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"#include <string.h>"                                                  +"\n"+
							"#include <stdio.h>"                                                   +"\n"+
							""                                                                     +"\n"+
							"void test7_1()"                                                       +"\n"+
							"{"                                                                    +"\n"+
							"	char* p;"                                                          +"\n"+
							"	p = (char*)malloc(sizeof(char)*2);"                                +"\n"+
							"	(p+1)[0] = 1; //DEFECT, NPD_EXP,p+1"                               +"\n"+
							"	free(p);"                                                          +"\n"+
							"}"
							,
							"gcc"
							,
							"NPD_EXP"
							,
				},
				//////////////////////////4//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"#include <string.h>"                                                  +"\n"+
							"#include <stdio.h>"                                                   +"\n"+
							""                                                                     +"\n"+
							"typedef struct _st1 {"                                                +"\n"+
							"	char str;"                                                         +"\n"+
							"}st1;"                                                                +"\n"+
							""                                                                     +"\n"+
							"void test8_1()"                                                       +"\n"+
							"{"                                                                    +"\n"+
							"	st1* pst;"                                                         +"\n"+
							"	pst = (st1*)malloc(sizeof(st1)*2);"                                +"\n"+
							"	(pst+1)->str = 'c';//DEFECT, NPD_EXP,pst+1"                        +"\n"+
							"	free(pst);"                                                        +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"NPD_EXP"
							,
				},
				//////////////////////////5//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"#include <string.h>"                                                  +"\n"+
							"#include <stdio.h>"                                                   +"\n"+
							""                                                                     +"\n"+
							"typedef struct _st22 {"                                               +"\n"+
							"	int a;"                                                              +"\n"+
							"}st22;"                                                               +"\n"+
							"typedef struct _st2 {"                                                +"\n"+
							"	st22* pst;"                                                          +"\n"+
							"	char* str;"                                                          +"\n"+
							"}st2;"                                                                +"\n"+
							""                                                                     +"\n"+
							"void test2_1(char to)"                                                +"\n"+
							"{"                                                                    +"\n"+
							"	st2 s;"                                                              +"\n"+
							"	s.str=(char*)malloc(13);"                                            +"\n"+
							"	s.str[0]=to; //DEFECT, NPD_EXP, s.str"                               +"\n"+
							"}"
							,
							"gcc"
							,
							"NPD_EXP"
							,
				},
				//////////////////////////6//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"#include <string.h>"                                                  +"\n"+
							"#include <stdio.h>"                                                   +"\n"+
							""                                                                     +"\n"+
							"typedef struct _st22 {"                                               +"\n"+
							"	int a;"                                                              +"\n"+
							"}st22;"                                                               +"\n"+
							"typedef struct _st2 {"                                                +"\n"+
							"	st22* pst;"                                                          +"\n"+
							"	char* str;"                                                          +"\n"+
							"}st2;"                                                                +"\n"+
							""                                                                     +"\n"+
							"void test2_2(st2* pst, char a)"                                       +"\n"+
							"{"                                                                    +"\n"+
							"	pst->str=(char*)malloc(13);"                                         +"\n"+
							"	pst->str[0] = a; //DEFECT, NPD_EXP, pst->str"                        +"\n"+
							"}"
							,
							"gcc"
							,
							"NPD_EXP"
							,
				},
				//////////////////////////7//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"#include <string.h>"                                                  +"\n"+
							"#include <stdio.h>"                                                   +"\n"+
							""                                                                     +"\n"+
							"typedef struct _st22 {"                                               +"\n"+
							"	int a;"                                                              +"\n"+
							"}st22;"                                                               +"\n"+
							"typedef struct _st2 {"                                                +"\n"+
							"	st22* pst;"                                                          +"\n"+
							"	char* str;"                                                          +"\n"+
							"}st2;"                                                                +"\n"+
							""                                                                    +"\n"+
							"void test2_3()"                                                       +"\n"+
							"{"                                                                    +"\n"+
							"	st2 s;"                                                              +"\n"+
							"	s.pst=(char*)malloc(sizeof(st22)*2);"                                +"\n"+
							"	s.pst->a=1; //DEFECT, NPD_EXP, s.pst"                                +"\n"+
							"}"
							,
							"gcc"
							,
							"NPD_EXP"
							,
				},
				//////////////////////////8//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"#include <string.h>"                                                  +"\n"+
							"#include <stdio.h>"                                                   +"\n"+
							""                                                                     +"\n"+
							"typedef struct _st22 {"                                               +"\n"+
							"	int a;"                                                              +"\n"+
							"}st22;"                                                               +"\n"+
							"typedef struct _st2 {"                                                +"\n"+
							"	st22* pst;"                                                          +"\n"+
							"	char* str;"                                                          +"\n"+
							"}st2;"                                                                +"\n"+
							""                                                                     +"\n"+
							"void test2_4(st2* pst)"                                               +"\n"+
							"{"                                                                    +"\n"+
							"	pst->pst=(char*)malloc(sizeof(st22)*2);"                             +"\n"+
							"	pst->pst->a = 1;//DEFECT, NPD_EXP, pst->pst"                         +"\n"+
							"}"
							,
							"gcc"
							,
							"NPD_EXP"
							,
				},
				//////////////////////////9//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"#include <string.h>"                                                  +"\n"+
							"#include <stdio.h>"                                                   +"\n"+
							""                                                                     +"\n"+
							"typedef struct _st22 {"                                               +"\n"+
							"	int a;"                                                              +"\n"+
							"}st22;"                                                               +"\n"+
							"typedef struct _st2 {"                                                +"\n"+
							"	st22* pst;"                                                          +"\n"+
							"	char* str;"                                                          +"\n"+
							"}st2;"                                                                +"\n"+
							""                                                                     +"\n"+
							"void test2_5(st2* pst, int a, char* str)"                             +"\n"+
							"{"                                                                    +"\n"+
							"	if (a > 1) {"                                                        +"\n"+
							"		pst->str=(char*)malloc(13);"                                        +"\n"+
							"	} else {"                                                            +"\n"+
							"		pst->str=str;"                                                    +"\n"+
							"	}"                                                                   +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				//////////////////////////10//////////////////////////////////////////////
				//jdh  需要修改 nmh
				//test2_2和test2_4中区间有问题
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"#include <string.h>"                                                  +"\n"+
							"#include <stdio.h>"                                                   +"\n"+
							""                                                                     +"\n"+
							"typedef struct _st22 {"                                               +"\n"+
							"	int a;"                                                              +"\n"+
							"}st22;"                                                               +"\n"+
							"typedef struct _st2 {"                                                +"\n"+
							"	st22* pst;"                                                          +"\n"+
							"	char* str;"                                                          +"\n"+
							"}st2;"                                                                +"\n"+
							""                                                                     +"\n"+
							"void test2_1(char to)"                                                +"\n"+
							"{"                                                                    +"\n"+
							"	st2 s;"                                                              +"\n"+
							"	s.str=(char*)malloc(13);"                                            +"\n"+
							"	if (s.str==0) {"                                                     +"\n"+
							"		return;"                                                            +"\n"+
							"	}"                                                                   +"\n"+
							"	s.str[0]=to; //FP"                                          +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void test2_2(char to)"                                                +"\n"+
							"{"                                                                    +"\n"+
							"	st2 s;"                                                              +"\n"+
							"	s.str=(char*)malloc(13);"                                            +"\n"+
							"	if (!s.str) {"                                                        +"\n"+
							"		return;"                                                            +"\n"+
							"	}"                                                                   +"\n"+
							"	s.str[0]=to; //FP"                                          +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void test2_3(char to)"                                                +"\n"+
							"{"                                                                    +"\n"+
							"	st2 s;"                                                              +"\n"+
							"	s.str=(char*)malloc(13);"                                            +"\n"+
							"	if (s.str!=0) {"                                                     +"\n"+
							"		s.str[0]=to; //FP"                                         +"\n"+
							"	}"                                                                   +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void test2_4(char to)"                                                +"\n"+
							"{"                                                                    +"\n"+
							"	st2 s;"                                                              +"\n"+
							"	s.str=(char*)malloc(13);"                                            +"\n"+
							"	if (s.str) {"                                                       +"\n"+
							"		s.str[0]=to; //FP"                                         +"\n"+
							"	}"                                                                   +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				//////////////////////////11//////////////////////////////////////////////
				{
					""                                                +"\n"+
							"#include <string.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"void zk_NPD_EXP1_1_f1(char *src)"                                      +"\n"+
							"{"                                                                    +"\n"+
							"	char c;"                                                             +"\n"+
							"	int len, i;"                                                         +"\n"+
							""                                                                     +"\n"+
							"	if (!src)"                                                           +"\n"+
							"		return;"                                                            +"\n"+
							"	len = strlen(src);"                                                  +"\n"+
							"	for (i = 0; i < len; i++) {"                                         +"\n"+
							"		c = *(src + i); //FP"                                               +"\n"+
							""                                                         +"\n"+
							"	}"                                                                   +"\n"+
							"	return;"                                                             +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				//////////////////////////12//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"void zk_NPD_EXP1_2_f1()"                                               +"\n"+
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
				//////////////////////////13//////////////////////////////////////////////
				{
					""                                                +"\n"+
							"#include <string.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"void zk_NPD_EXP1_1_f1(char *src)"                                      +"\n"+
							"{"                                                                    +"\n"+
							"	char c;"                                                             +"\n"+
							"	int len, i;"                                                         +"\n"+
							""                                                                     +"\n"+
							"	if (!src)"                                                           +"\n"+
							"		return;"                                                            +"\n"+
							"	len = strlen(src);"                                                  +"\n"+
							"	for (i = 0; i < len; i++) {"                                         +"\n"+
							"		c = *(src + i); //FP"                                               +"\n"+
							""                                                         +"\n"+
							"	}"                                                                   +"\n"+
							"	return;"                                                             +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				//////////////////////////14//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"#include <string.h>"                                                  +"\n"+
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
							"        *(s + i) = *(b + i);//DEFECT,NPD_EXP,s+i"                                 +"\n"+
							"	}"                                                                   +"\n"+
							"    *(s + m) = NULL;//DEFECT,NPD_EXP,s+m"                                                 +"\n"+
							"    return (s);"                                                      +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"NPD_EXP"
							,
				},
				//////////////////////////15//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"void zk_NPD_EXP1_2_f1()"                                               +"\n"+
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
				//////////////////////////16//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"#include <stdio.h>"                                                   +"\n"+
							""                                                                     +"\n"+
							"void test1_1(int *p)"                                                 +"\n"+
							"{"                                                                    +"\n"+
							"	int a = 0;"                                                          +"\n"+
							"	if (p) {"                                                            +"\n"+
							"		a = 1;"                                                             +"\n"+
							"	}"                                                                   +"\n"+
							"	*(p+1) = 1;//DEFECT, NPD_EXP,p+1"                                    +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"NPD_EXP"
							,
				},
				////////////////////////////17//////////////////////////////////////////////
				//这个用例应该是NPD。已经移到了NPD中
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
							"OK"
							,
				},
				//////////////////////////18//////////////////////////////////////////////	
				{
					"#include<stdlib.h>"                                                   +"\n"+
							"typedef struct {"                                                     +"\n"+
							"    int *adbuf;"                                                      +"\n"+
							"    int adbufsize;"                                                   +"\n"+
							"} ad;"                                                                +"\n"+
							""                                                                     +"\n"+
							"ad * ad_init()"                                                       +"\n"+
							"{"                                                                    +"\n"+
							"    ad *r;"                                                           +"\n"+
							""                                                                     +"\n"+
							"    if ((r = (ad *)malloc(sizeof(*r))) == NULL) {"                    +"\n"+
							"        return NULL;"                                                 +"\n"+
							"    }"                                                                +"\n"+
							""                                                                     +"\n"+
							"    if ((r->adbuf = (int*)malloc(r->adbufsize * sizeof(*r->adbuf))) == NULL) {//FP"+"\n"+
							"        free(r);"                                                     +"\n"+
							"        return NULL;"                                                 +"\n"+
							"    }"                                                                +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
								
				/////////////////////////19/////////////////////////////////////////////
				{
					"#include <stdio.h>"                                                   +"\n"+
							"struct jhb_NPD_EXP1_1_s1 {"                                            +"\n"+
							"	int m;"                                                              +"\n"+
							"	struct jhb_NPD_EXP1_1_s1 * next;"                                            +"\n"+
							"};"                                                                   +"\n"+
							"void jhb_NPD_EXP1_1_f1(struct jhb_NPD_EXP1_1_s1 * node){"                      +"\n"+
							"	struct jhb_NPD_EXP1_1_s1 * a;"                                               +"\n"+
							"	if (node->next!=NULL)"                                               +"\n"+
							"		a=node->next;"                                                      +"\n"+
							"	if (node->next->next==NULL)   //DEFECT"                               +"\n"+
							"	{"                                                                   +"\n"+
							"	}"                                                                   +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"NPD_EXP"
							,
				},
				/////////////////////////  20 ///////////////////
				//jdh  需要修改  nmh
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"#define MAX 10"                                                       +"\n"+
							"typedef struct{"                                                          +"\n"+
							"	char*s;"                                                             +"\n"+
							"	char a[MAX];"                                                        +"\n"+
							"} str;"                                                                   +"\n"+
							""                                                                     +"\n"+
							"str* fun(){"                                                          +"\n"+
							"	return (str*)malloc(sizeof(str)*MAX);"                               +"\n"+
							"}"                                                                    +"\n"+
							"void fun1(str **p){"                                                  +"\n"+
							"	if(*p==NULL)"                                                        +"\n"+
							"		*p=fun();"                                                          +"\n"+
							"	(*p)->a[1]='1';  //DEFECT"                                           +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"NPD_EXP"
							,
				},

				///////////////// 21 ///////////////////	
				{
					""                                                                     +"\n"+
							"void func1(int **p){"                                                     +"\n"+
							"   int a;"                                                           +"\n"+
							"   if(*p)"                                                           +"\n"+
							"   {a = 1;}"                                                                 +"\n"+
							"   **p;"                                                              +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"NPD_EXP"
							,
				},
		});
	}
}
