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
public class UVF_P extends ModelTestBase{
	public UVF_P(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/UVF_P-0.1.xml";
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
				//总用例：42
				//未通过用例：1
				//未通过用例序号:39
////////////////////////////0  ///////////////////////////////////////////
				{
					        "#include<stdlib.h>    "                                               +"\n"+
					        "#include<stdio.h>"                                                     +"\n"+
							"int test_uvf_p_1(){"                                                  +"\n"+
							"    int *p=malloc(sizeof(int)*3);"                                               +"\n"+
							"    int a=*p;//defect"                                                +"\n"+
							"    return 0;"                                                        +"\n"+
							"    }" 
							,
							"gcc"
							,
							"UVF_P"
							,
				},	
///////////////////////////////1/////////////////////////////////
				{
					        "#include<stdlib.h>    "                                               +"\n"+
					        "#include<stdio.h>"                                                     +"\n"+
							"int test_uvf_p_2(){"                                                  +"\n"+
							"int* p=malloc(sizeof(int)*3);"                                       +"\n"+
							"p[0]=p[1];//defect,p[1],uvf_p"                                               +"\n"+
							"return 0;"                                                        +"\n"+
							"}" 
							,
							"gcc"
							,
							"UVF_P"
							,
				},
//////////////////////////2/////////////////////////////////////////////
				{
					"#include<stdlib.h>    "                                            +"\n"+
					"#include<stdio.h>"                                                 +"\n"+
							"int ffffff(){"                                             +"\n"+
							"int p;"                                                    +"\n"+
							"int* t=(int*)malloc(sizeof(int)*3);;"                      +"\n"+
							"p=t[0];//defect,t[0],uvf_p"                                                   +"\n"+
							"return 0;"                                                 +"\n"+
							"} " 
							,
							"gcc"
							,
							"UVF_P"
							,
				},
///////////////////////////////3/////////////////////////////////
				{
					        "#include<stdlib.h>    "                                               +"\n"+
					        "#include<stdio.h>"                                                     +"\n"+
							"int test_uvf_p_2(){"                                                  +"\n"+
							"    int *p;"                                                          +"\n"+
							"    p=malloc(sizeof(int)*3);"                                       +"\n"+
							"    int a[3];"                                                        +"\n"+
							"    a[0]=p[1];//defect,p[1],uvf_p"                                               +"\n"+
							"    return 0;"                                                        +"\n"+
							"    }" 
							,
							"gcc"
							,
							"UVF_P"
							,
				},
		
//////////////////////////4 //////////////////////////////////////////////
				{//UVF_P
					"#include<stdlib.h>    "                                               +"\n"+
					"#include<stdio.h>"                                                     +"\n"+
					"void f1(int *a,int *b){"                                          +"\n"+
					"int a1=a[1]; "  +"\n"+
					"int b1=b[1];"                                                +"\n"+
					"	"                                                                    +"\n"+
					"}"                                                                    +"\n"+
					"int main(){"                                                              +"\n"+
					"int *x=(int *)malloc(sizeof(int)*4); "  +"\n"+
					"int *y=(int *)malloc(sizeof(int)*4);"                              +"\n"+
					"f1(x,y);"                                                          +"\n"+
					"}"
					,
					"gcc"
					,
					"UVF_P"
					,
				},		
				////////////////////////////////////////////5   ///////////////////	
				{           "#include<stdlib.h>    "                                               +"\n"+
					        "#include<stdio.h>    "                                               +"\n"+
							"int main(){"                                                          +"\n"+
							"    char *q=(char *)malloc(sizeof(char)*4);"                          +"\n"+
							"    char *p=\"abc\\0\"; char *r;"                                                 +"\n"+
							"	char d=p[0];"                                                        +"\n"+
							"	char c=q[0];//defect,uvf_p,q"                                        +"\n"+
							"	char b=r[0];"                                                        +"\n"+
							"    printf(\"%c\",c);"                                                  +"\n"+
							"    system(\"pause\");"                                                 +"\n"+
							"    return 0;"                                                        +"\n"+
							"    }"                                                                
							,
							"gcc"
							,
							"UVF_P"
							,
				},		
				////////////////////////6/////////////////////////////////////////////
				{
					"void test1(int i) "                                                   +"\n"+
					"{"                                                                    +"\n"+
					"	int *c;"                                                             +"\n"+
					"	switch(i){"                                                          +"\n"+
					"	case 1:"                                                             +"\n"+
					"	default:"                                                            +"\n"+
					"		c=&i;"                                                              +"\n"+
					"		break;"                                                             +"\n"+
					"	case 2:"                                                             +"\n"+
					"		c=&i;"                                                              +"\n"+
					"		break;"                                                             +"\n"+
					"	case 3:"                                                             +"\n"+
					"		break;"                                                             +"\n"+
					"	}"                                                                   +"\n"+
					"    c++;   //DEFECT,UVF,c"                                            +"\n"+
					"}"                            
							,
							"gcc"
							,
							"OK"
							,
				},		
///////////////////////////////////////7///////////////////////////////
				{
					"#include<stdlib.h>    "                                               +"\n"+
					"#include<stdio.h>"                                                     +"\n"+
					"#define SIZE 128"                                               +"\n"+
					"int zk_uvf_2_f1(int flag)"                                            +"\n"+
					"{"                                                                    +"\n"+
					"	int array[SIZE];"                                                    +"\n"+
					"	if (flag > 0) {"                                                     +"\n"+
					"		array[0]=1;"                                                        +"\n"+
					"	}"                                                                   +"\n"+
					"	return *array;"                                             +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"OK"
					,
				},
/////////////////////////8/////////////////////////////////////////////
				{
					"#include<stdlib.h>    "                                               +"\n"+
					"#include<stdio.h>"                                                     +"\n"+
					"#include<string.h>"                                                     +"\n"+
					"f(int a){"                                                            +"\n"+
					"    char * x ;"                                                       +"\n"+
					"    if (a) {x= (char*)malloc(1);}"                                      +"\n"+
					"    free(x); //DEFECT"                                                +"\n"+
					"  }int main() {return 0;}"                                                                  
					,
					"gcc"
					,
					"OK"
					,
				},			
/////////////////////////9/////////////////////////////////////////////
				{
					"#include <stdlib.h>  "                                                +"\n"+
					"#include <string.h>"                                                  +"\n"+
					"int main(){"                                                          +"\n"+
					"	int* s=(char*)malloc(100);"                                         +"\n"+
					"	int a[100];"                                                        +"\n"+
					"	strcpy(a,s); //DEFECT"                                               +"\n"+
					"	return 0;"                                                           +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"UVF_P"
					,
				},	
/////////////////  10   ///////////////////	
	            {
	            "int ff() {"                                                           +"\n"+
	            "	int *c = (int *) malloc(5*sizeof(int));"                             +"\n"+
	            "	if (c == NULL) "                                                     +"\n"+
	            "		return 0;"                                                          +"\n"+
	            "	return 1;"                                                           +"\n"+
	            "}"                                                                    
	            ,
				"gcc"
				,
				"OK"
				,
	            },
/////////////////  11   ///////////////////	
	            {
	            "int ff(int *fd) {"                                                    +"\n"+
	            "	int * p=fd;"                                                         +"\n"+
	            "	int result=2;"                                                       +"\n"+
	            "	p += result;"                                                        +"\n"+
	            "	return 0;"                                                           +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "OK"
	            ,
	            },
/////////////////  12   ///////////////////	
	            {
	            "int ff() {"                                                           +"\n"+
	            "	char* s=(char*)malloc(100);"                                         +"\n"+
	            "	memset(s,'a',100);"                                                  +"\n"+
	            "	char d=s[0];"                                                        +"\n"+
	            "	return 0;"                                                           +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "OK"
	            ,
	            },
//////////////////////////  13 //////////////////////////////////////////////
				 {//函数副作用考虑
					 "#include <string.h>"                                                  +"\n"+
					 "#include<stdlib.h> "                                                  +"\n"+
			          "#include<stdio.h>"                                                   +"\n"+
					 "void f1(int *a){"                                                     +"\n"+
					 "a[0]=1;"                                    +"\n"+
					 "a=(int *)malloc(sizeof(int *)*5);"                                    +"\n"+
					 "a[0]=9;"                                                              +"\n"+
					 "}"                                                                    +"\n"+
					 "int main(){"                                                          +"\n"+
					 "	int *x=(int *)malloc(sizeof(int *)*5);"                           +"\n"+
					 "	f1(x);"                           +"\n"+
					 "	int t=x[0];"                                                        +"\n"+
					 "	return 0;"                                                          +"\n"+
					 "}"
					 ,
					 "gcc"
					 ,
					 "OK"
					 ,
					 },	
//////////////////////////14//////////////////////////////////////////////
						{
							"extern void ifoo(int a){};"                                           +"\n"+
									"void uninit_array_must() {"                                           +"\n"+
									"      int a[10];"                                                     +"\n"+
									"      ifoo(a[1]); //defect"                                           +"\n"+
									"}"                                                                  
									,
									"gcc"
									,
									"OK"
									,
						},		
//////////////////////////15//////////////////////////////////////////////
						{
							"extern void pfoo(int *p) {return;};"                                  +"\n"+
							"extern int some_condition(){return 1;};"                              +"\n"+
							"void uninit_array_might() {"                                         +"\n"+
							"      int a[10];"                                                    +"\n"+
							"      if (some_condition()) {"                                        +"\n"+
							"          int i;"                                                     +"\n"+
							"          for(i = 0; i < 10; i++) {"                                  +"\n"+
							"              a[i] = 0;"                                              +"\n"+
							"         }"                                                           +"\n"+
							"     }"                                                               +"\n"+
							"     pfoo(a[4]);"                                            +"\n"+
							"}"                                                                   
							,
							"gcc"
							,
							"OK"
							,
						},
////////////////////////////16  ///////////////////////////////////////////
						{
							        "#include<stdlib.h>    "                                               +"\n"+
							        "#include<stdio.h>"                                                     +"\n"+
									"int test_uvf_p_1(){"                                                  +"\n"+
									"    int *p=malloc(sizeof(int)*3);"                                               +"\n"+
									"    int *a=p;"                                                +"\n"+
									"    return 0;"                                                        +"\n"+
									"    }" 
									,
									"gcc"
									,
									"OK"
									,
						},	
///////////////////////////////17/////////////////////////////////
						{
							        "#include<stdlib.h>    "                                               +"\n"+
							        "#include<stdio.h>"                                                     +"\n"+
									"int test_uvf_p_2(){"                                                  +"\n"+
									"int* p=malloc(sizeof(int)*3);"                                       +"\n"+
									"p[0]=1;"                                               +"\n"+
									"return p[0];"                                                        +"\n"+
									"}" 
									,
									"gcc"
									,
									"OK"
									,
						},	
///////////////////////////////18/////////////////////////////////
						{
							        "#include<stdlib.h>    "                                               +"\n"+
							        "#include<stdio.h>"                                                     +"\n"+
									"int test_uvf_p_2(){"                                                  +"\n"+
									"int* p=malloc(sizeof(int)*3);"                                       +"\n"+
									"p[0]=1;"                                               +"\n"+
									"return *p;"                                                        +"\n"+
									"}" 
									,
									"gcc"
									,
									"OK"
									,
						},	
///////////////////////////////19/////////////////////////////////
						{
							        "#include<stdlib.h>    "                                               +"\n"+
							        "#include<stdio.h>"                                                     +"\n"+
									"int test_uvf_p_2(){"                                                  +"\n"+
									"int* p=malloc(sizeof(int)*3);"                                       +"\n"+
									"*p=1;"                                               +"\n"+
									"return p[0];"                                                        +"\n"+
									"}" 
									,
									"gcc"
									,
									"OK"
									,
						},	
///////////////////////////////20/////////////////////////////////
						{
							        "#include<stdlib.h>    "                                               +"\n"+
							        "#include<stdio.h>"                                                     +"\n"+
									"int test_uvf_p_2(){"                                                  +"\n"+
									"int* p=malloc(sizeof(int)*3);"                                       +"\n"+
									"p[0]=1;"                                               +"\n"+
									"return p[2];"                                                        +"\n"+
									"}" 
									,
									"gcc"
									,
									"UVF_P"
									,
						},	
/////////////////  21   ///////////////////	
			            {
			            "#include<string.h>"                                                   +"\n"+
			            "#include<stdlib.h> "                                                  +"\n"+
			            "#include<stdio.h>"                                                    +"\n"+
			            "char *a; "                                                            +"\n"+
			            "char ff1(char *p,int flag){"                                          +"\n"+
			            "if(flag>0){"                                                          +"\n"+
			            "a[0]='w';"                                                            +"\n"+
			            "}else{"                                                               +"\n"+
			            "a[1]='x';"                                                            +"\n"+
			            "}"                                                                    +"\n"+
			            "return p[0];"                                                         +"\n"+
			            "}   "                                                                 +"\n"+
			            ""                                                                     +"\n"+
			            "int main(){"                                                          +"\n"+
			            "    char *q=(char *)malloc(sizeof(char)*4);"                          +"\n"+
			            "    char *p=(char *)malloc(sizeof(char)*4);"                                                 +"\n"+
			            "    a=(char *)malloc(sizeof(char *)*5);"                              +"\n"+
			            "    int t=1;"                                                         +"\n"+
			            "    q[0]=ff1(p,t);//UVF_P"                                                   +"\n"+
			            "    a[2]='w';"                                                        +"\n"+
			            "	return 0;"                                                           +"\n"+
			            "    }"                                                                
			            ,
			            "gcc"
			            ,
			            "UVF_P"
			            ,
			            },
////////////////////////////////22   ////////////////////////////////////////	
			            {
			            "#include<string.h>"                                                   +"\n"+
			            "#include<stdlib.h>"                                                   +"\n"+
			            "#include<stdio.h>"                                                    +"\n"+
			            "char ff_22(char *b,char *c){"                                            +"\n"+
			            "     int i=1;"                                                        +"\n"+
			            "     char a=b[0];"                                                    +"\n"+
			            "     if(i==1){"                                                       +"\n"+
			            "      a=c[1];        "                                                +"\n"+
			            "      }"                                                              +"\n"+
			            "      if(a==c[1])"                                                    +"\n"+
			            "      return a;"                                                      +"\n"+
			            "      else"                                                           +"\n"+
			            "      return c[1];    "                                               +"\n"+
			            "    }"                                                                +"\n"+
			            "int main(){"                                                          +"\n"+
			            "    char *q=(char *)malloc(sizeof(char)*4);"                          +"\n"+
			            "    char *p=\"abc\\0\";"                                                 +"\n"+
			            "    char c=ff_22(p,q);   //defect,UVF_P,q"                                  +"\n"+
			            "    return 0;"                                                        +"\n"+
			            "    }"                                                                
			            ,
			            "gcc"
			            ,
			            "UVF_P"
			            ,
			            },
/////////////////  23   ///////////////////	
			            {
			            "#include<string.h>"                                                   +"\n"+
			            "#include<stdlib.h>"                                                   +"\n"+
			            "#include<stdio.h>"                                                    +"\n"+
			            "char fff_23(char *w,char *y){"                                           +"\n"+
			            "     char x;"                                                         +"\n"+
			            "     if(w[1]>=y[1])"                                                  +"\n"+
			            "         x=w[1];"                                                     +"\n"+
			            "     else"                                                            +"\n"+
			            "         x=y[1];"                                                     +"\n"+
			            "     return x;"                                                       +"\n"+
			            "     }"                                                               +"\n"+
			            ""                                                                     +"\n"+
			            "char ff_23(char *b,char *c){"                                            +"\n"+
			            "     char a;"                                                         +"\n"+
			            "     a=fff_23(b,c);"                                                     +"\n"+
			            "     return a;    "                                                   +"\n"+
			            "    }"                                                                +"\n"+
			            "    "                                                                 +"\n"+
			            "int main(){"                                                          +"\n"+
			            "    char *q=(char *)malloc(sizeof(char)*4);"                          +"\n"+
			            "    char *p=\"abc\\0\";"                                                 +"\n"+
			            "    char c=ff_23(p,q);//defect,UVF_P,q"                                  +"\n"+
			            "    printf(\"%c\",c);"                                                  +"\n"+
			            "    system(\"pause\");"                                                 +"\n"+
			            "    return 0;"                                                        +"\n"+
			            "    }"                                                                
			            ,
			            "gcc"
			            ,
			            "UVF_P"
			            ,
			            },
/////////////////  24   ///////////////////	
			            {
			            "#include<string.h>"                                                   +"\n"+
			            "#include<stdlib.h>"                                                   +"\n"+
			            "#include<stdio.h>"                                                    +"\n"+
			            "char fff_24(char *w,char *y){"                                           +"\n"+
			            "     char x;"                                                         +"\n"+
			            "     if(w[1]>=y[1])"                                                  +"\n"+
			            "         x=w[1];"                                                     +"\n"+
			            "     else"                                                            +"\n"+
			            "         x=y[1];"                                                     +"\n"+
			            "     return x;"                                                       +"\n"+
			            "     }"                                                               +"\n"+
			            ""                                                                     +"\n"+
			            "char ff_24(char *b,char *c){"                                            +"\n"+
			            "     char a;"                                                         +"\n"+
			            "     a=fff_24(b,c);"                                                     +"\n"+
			            "     return a;    "                                                   +"\n"+
			            "    }"                                                                +"\n"+
			            "    "                                                                 +"\n"+
			            "int main_24(){"                                                          +"\n"+
			            "    char *q=\"efg\\0\";"                          +"\n"+
			            "    char *p=\"abc\\0\";"                                                 +"\n"+
			            "    char c=ff_24(p,q);"                                  +"\n"+
			            "    printf(\"%c\",c);"                                                  +"\n"+
			            "    system(\"pause\");"                                                 +"\n"+
			            "    return 0;"                                                        +"\n"+
			            "    }"                                                                
			            ,
			            "gcc"
			            ,
			            "OK"
			            ,
			            },			
/////////////////  25   ///////////////////	
			            {
			            "#include<string.h>"                                                   +"\n"+
			            "#include<stdlib.h> "                                                  +"\n"+
			            "#include<stdio.h>"                                                    +"\n"+
			            "char *a; "                                                            +"\n"+
			            "char ff1_25(char *p){"                                                   +"\n"+
			            "a[0]='w';"                                                            +"\n"+
			            "return p[0];"                                                         +"\n"+
			            "}   "                                                                 +"\n"+
			            ""                                                                     +"\n"+
			            "int main_25(){"                                                          +"\n"+
			            "    char *q=(char *)malloc(sizeof(char)*4);"                          +"\n"+
			            "    char *p=\"abc\\0\";"                                                 +"\n"+
			            "    a=(char *)malloc(sizeof(char *)*5);"                              +"\n"+
			            "    q[0]=ff1_25(p);"                                                     +"\n"+
			            "    a[2]='w';"                                                        +"\n"+
			            "	return 0;"                                                           +"\n"+
			            "    }"                                                                
			            ,
			            "gcc"
			            ,
			            "OK"
			            ,
			            },
//////////////////////////  26 //////////////////////////////////////////////
						 {//属于过程间
							 "#include <string.h>"                                                  +"\n"+
							 "#include<stdlib.h> "                                                  +"\n"+
					          "#include<stdio.h>"                                                    +"\n"+
							 "void f1_26(int *a,int *b){"                                          +"\n"+
							 "	int a1=a[1]; int b1=b[1];"                                                +"\n"+
							 "}"                                                                    +"\n"+
							 "int main(){"                                                              +"\n"+
							 "	int *x; int *y=(int *)malloc(sizeof(int)*5);"                                                          +"\n"+
							 "	f1_26(x,y);"                                                          +"\n"+
							 "}"
							 ,
							 "gcc"
							 ,
							 "UVF_P"
							 ,
							 },	
//////////////////////////27 //////////////////////////////////////////////
							 {//属于过程间
								 "#include <string.h>"                                                  +"\n"+
								 "#include<stdlib.h> "                                                  +"\n"+
						          "#include<stdio.h>"                                                    +"\n"+
								 "void f1_27(int *a,int *b){"                                          +"\n"+
								 "	int a1=a[1]; int b1=b[1];"                                                +"\n"+
								 "	"                                                                    +"\n"+
								 "}"                                                                    +"\n"+
								 "int main_27(){"                                                              +"\n"+
								 "	int *x=(int *)malloc(sizeof(int *)*5); "                                                          +"\n"+
								 "  int *y=(int *)malloc(sizeof(int *)*5);"                                                          +"\n"+
								 "	x[0]=1;"                                                          +"\n"+
								 "	y[0]=2;"                                                          +"\n"+
								 "	f1_27(x,y);"                                                          +"\n"+
								 "}"
								 ,
								 "gcc"
								 ,
								 "UVF_P"
								 ,
								 },
//////////////////////////28 //////////////////////////////////////////////
								 {//属于过程间
									 "#include <string.h>"                                                  +"\n"+
									 "#include<stdlib.h> "                                                  +"\n"+
							         "#include<stdio.h>"                                                    +"\n"+
									 "void f1_28(int *a,int *b){"                                          +"\n"+
									 "	int a1=a[1]; int b1=b[1];"                                                +"\n"+
									 "}"                                                                    +"\n"+
									 "int main_28(){"                                                              +"\n"+
									 "	int *x=(int *)malloc(sizeof(int)*5); int *y=(int *)malloc(sizeof(int)*5);"                                                          +"\n"+
									 "	f1_28(x,y);"                                                          +"\n"+
									 "}"
									 ,
									 "gcc"
									 ,
									 "UVF_P"
									 ,
									 },		
//////////////////////////29 //////////////////////////////////////////////
									 {//属于过程间
										 "#include <string.h>"                                                  +"\n"+
										 "#include<stdlib.h> "                                                  +"\n"+
								         "#include<stdio.h>"                                                    +"\n"+
										 "void f1_29(int *a){"                                          +"\n"+
										 "	int *a1=a; "                                                +"\n"+
										 "	"                                                                    +"\n"+
										 "}"                                                                    +"\n"+
										 "int main_29(){"                                                              +"\n"+
										 "	int *x=(int *)malloc(sizeof(int)*5);;"                                                          +"\n"+
										 "	f1_29(x);"                                                          +"\n"+
										 "}"
										 ,
										 "gcc"
										 ,
										 "OK"
										 ,
										 },	
//////////////////////////30 //////////////////////////////////////////////
										 {//属于过程间
											 "#include <string.h>"                                                  +"\n"+
											 "#include<stdlib.h> "                                                  +"\n"+
									            "#include<stdio.h>"                                                    +"\n"+
											 "void f1_30(int *a){"                                          +"\n"+
											 "	int *a1=a; "                                                +"\n"+
											 "	"                                                                    +"\n"+
											 "}"                                                                    +"\n"+
											 "int main_30(){"                                                              +"\n"+
											 "	int *x=(int *)malloc(sizeof(int *)*5);"                                                          +"\n"+
											 "	f1(x);"                                                          +"\n"+
											 "}"
											 ,
											 "gcc"
											 ,
											 "OK"
											 ,
											 },	
//////////////////////////31 //////////////////////////////////////////////
											 {//属于过程间
												 "#include <string.h>"                                                  +"\n"+
												 "#include<stdlib.h> "                                                  +"\n"+
										         "#include<stdio.h>"                                                    +"\n"+
												 "void f1_31(int *a){"                                          +"\n"+
												 "	int *a1=a; "                                                +"\n"+
												 "	"                                                                    +"\n"+
												 "}"                                                                    +"\n"+
												 "int main(){"                                                              +"\n"+
												 "	int *x=(int *)malloc(sizeof(int *)*5);"                                                          +"\n"+
												 "	x[0]=1;"                                                          +"\n"+
												 "	f1_31(x);"                                                          +"\n"+
												 "}"
												 ,
												 "gcc"
												 ,
												 "OK"
												 ,
												 },	


//////////////////////////32/////////////////////////////////////////////	
										            {
										            "#include<string.h>"                                                     +"\n"+
										            "#include<stdlib.h> "                                                  +"\n"+
										            "#include<stdio.h>"                                                    +"\n"+
										            "char  *a; "                                                            +"\n"+
										            "char ff1_32(char *p){"                                                   +"\n"+
										            "a[0]=p[0];"                                                            +"\n"+
										            "char c=p[1];"                                                           +"\n"+
										            "return c;"                                                         +"\n"+
										            "} "                                                                   +"\n"+
										            ""                                                                     +"\n"+
										            "char ff2_32(char *e){"                                                   +"\n"+
										            "     char g=ff1_32(e);"                                                  +"\n"+
										            "     return g;"                                                       +"\n"+
										            "     }  "                                                             +"\n"+
										            ""                                                                     +"\n"+
										            "int main_32(){"                                                          +"\n"+
										            "   a=(char *)malloc(sizeof(char *)*8);"                               +"\n"+
										            "    char *q=\"abc\\0\";"                                                 +"\n"+
										            "    char b=ff2_32(q);"                                 +"\n"+
										            "	cout<<q<<endl;"                                                      +"\n"+
										            "	system(\"pause\");"                                                    +"\n"+
										            "	return 0;"                                                           +"\n"+
										            "    }"                                                                
										            ,
										            "gcc"
										            ,
										            "OK"
										            ,
										            },			
//////////////////////////33//////////////////////////////////////////////
										            {
											            "#include<string.h>"                                                     +"\n"+
											            "#include<stdlib.h> "                                                  +"\n"+
											            "#include<stdio.h>"                                                    +"\n"+
										            "f1_33(int *a,int *b, char* s){"                                          +"\n"+
										            "	char a1=s[0]; "                                                +"\n"+
										            "	"                                                                    +"\n"+
										            "}"                                                                    +"\n"+
						     			            "main_33(){"                                                              +"\n"+
										            "	char *a=(char *)malloc(sizeof(char *)*3);"                                                          +"\n"+
										            "	char  *b; char *c; int d;"                                                          +"\n"+
										            "	f1_33(b,c,a);"                                                          +"\n"+
										            "}"                                                                    
										            ,
										            "gcc"
										            ,
										            "UVF_P"
										            ,
										            },
//////////////////////////34/////////////////////////////////////////////
										            {
										            "#include <string.h>"                                                  +"\n"+
										            "#include <stdio.h>"                                                   +"\n"+
										            "char* p=(char *)malloc(sizeof(char *)*1);"                                                    +"\n"+
										            "void f_34(char* a){"                                                          +"\n"+
										            "	*p=*a;"                                                              +"\n"+
										            "	p=a;"                                                                +"\n"+
										            "}"                                                                    +"\n"+
										            "main(){"                                                              +"\n"+
										            ""                                                                     +"\n"+
										            "	char *b=(char *)malloc(sizeof(char *)*12);"                                                         +"\n"+
										            "	b[0]=1;"                                                               +"\n"+
										            "	f_34(b);"                                                               +"\n"+
										            ""                                                                     +"\n"+
										            ""                                                                     +"\n"+
										            "}"                                                                    
										            ,
										            "gcc"
										            ,
										            "OK"
										            ,
										            },
///////////////////////////////////35/////////////////////////////////////
										            {
										                "void ff_35(int *b){"                                                     +"\n"+
										                "     b++;"                                                            +"\n"+
										                "     return ;"                                                        +"\n"+
										                "     }"                                                               +"\n"+
										                "int aa_35(){"                                                            +"\n"+
										                "    int *a;"                                                          +"\n"+
										                "    ff_35(a);//defect"                                                           +"\n"+
										                "    return 0;"                                                        +"\n"+
										                "    } "                                                               
										                ,
										                "gcc"
										                ,
										                "OK"
											            ,
										            },
//////////////////////////36/////////////////////////////////////////////
										            {
										            "#include <string.h>"                                                  +"\n"+
										            "#include <stdio.h>"                                                   +"\n"+
										            "char* p=(char *)malloc(sizeof(char *)*1);"                                                    +"\n"+
										            "void f_36(char* a){"                                                          +"\n"+
										            "	*p=*a;"                                                              +"\n"+
										            "	p=a;"                                                                +"\n"+
										            "}"                                                                    +"\n"+
										            "main_36(){"                                                              +"\n"+
										            ""                                                                     +"\n"+
										            "	char *b=(char *)malloc(sizeof(char)*12);"                                                         +"\n"+
										            "	f_36(b);//defect"                                                               +"\n"+
										            ""                                                                     +"\n"+
										            ""                                                                     +"\n"+
										            "}"                                                                    
										            ,
										            "gcc"
										            ,
										            "UVF_P"
										            ,
										            },
/////////////////  37   ///////////////////	
										            {
										            "int main_37(){"                                                       +"\n"+
										            "int *x=(int *)malloc(sizeof(int *)*5);"                               +"\n"+
										            "int i=0;"                                                             +"\n"+
										            "for(i=0;i<3;i++){"                                                    +"\n"+
										            "x[i]=i;"                                                              +"\n"+
										            "}"                                                                    +"\n"+
										            "int t=x[2];"                                                          +"\n"+
										            "}"                                                                    
										            ,
										            "gcc"
										            ,
										            "OK"
										            ,
										            },
/////////////////  38   ///////////////////	
										            {
										            "int main_38(){"                                                       +"\n"+
										            "int *x=(int *)malloc(sizeof(int *)*5);"                               +"\n"+
										            "int i=0;"                                                             +"\n"+
										            "for(i=0;i<3;i++){"                                                    +"\n"+
										            "x[i]=i;"                                                              +"\n"+
										            "}"                                                                    +"\n"+
										            "int t=x[4];"                                                          +"\n"+
										            "}"                                                                    
										            ,
										            "gcc"
										            ,
										            "UVF_P"
										            ,
										            },
/////////////////  39   ///////////////////	
//下标区间不准确，提交给董玉坤
										            {
										            "int main_38(){"                                                       +"\n"+
										            "int *x=(int *)malloc(sizeof(int *)*5);"                               +"\n"+
										            "int i=0;"                                                             +"\n"+
										            "x[i++]=4;"                                                              +"\n"+
										            "int t=x[0];"                                                          +"\n"+
										            "}"                                                                    
										            ,
										            "gcc"
										            ,
										            "OK"
										            ,
										            },
/////////////////  40   ///////////////////	
										            {
										            "int * ff_40(int *a){"                                                 +"\n"+
										            "	return a;"                                                           +"\n"+
										            "}"                                                                    +"\n"+
										            "int main_40(){"                                                       +"\n"+
										            "int *x=(int *)malloc(sizeof(int *)*5);"                               +"\n"+
										            "int *i=ff_40(x);"                                                     +"\n"+
										            "int t=i[3];"                                                          +"\n"+
										            "}"                                                                    
										            ,
										            "gcc"
										            ,
										            "OK"
										            ,
										            },
/////////////////  41   ///////////////////	
										            {
										            "int main_41(){"                                                       +"\n"+
										            "int *x=(int *)malloc(sizeof(int *)*5);"                               +"\n"+
										            "x=(int *)malloc(sizeof(*x));"                                                     +"\n"+
										            "}"                                                                    
										            ,
										            "gcc"
										            ,
										            "OK"
										            ,
										            },
										            
										            
/////////////////  42   ///////////////////	
										            {
										            "int main_41(){"                                                       +"\n"+
										            "int *x=(int *)malloc(sizeof(int *)*5);"                               +"\n"+
										            "x=(int *)malloc(sizeof(*x));"                                                     +"\n"+
										            "}"                                                                    
										            ,
										            "gcc"
										            ,
										            "OK"
										            ,
										            },
/////////////////  43   ///////////////////	
										            {
										            "int main_41(){"                                                       +"\n"+
										            "int *x=(int *)malloc(sizeof(int *)*5);"                               +"\n"+
										            "x=(int *)malloc(sizeof(*x));"                                                     +"\n"+
										            "}"                                                                    
										            ,
										            "gcc"
										            ,
										            "OK"
										            ,
										            },
/////////////////  44   ///////////////////	
										            {
										            "void ff(int *a,int flag){"                                            +"\n"+
										            "int *ptr1;"                                                           +"\n"+
										            "int *ptr2;" 														+"\n"+
										            "int i;"                                                           +"\n"+
										            "if(flag>0){"                                                          +"\n"+
										            "	for (i=1;i<7;i++) {      "                                           +"\n"+
										            "    	ptr1 = a; 	/* target */"                                         +"\n"+
										            "       ptr2 = a;	/* source */"                                       +"\n"+
										            "       strcpy(ptr1, ptr2);"                                          +"\n"+
										            "	    if (flag==1) {"                                       +"\n"+
										            "			/* mirror this */"                                                 +"\n"+
										            "			ptr1[0] = ptr2[3];"                                                +"\n"+
										            "			ptr1[1] = ptr2[2];"                                                +"\n"+
										            "			ptr1[2] = ptr2[1];"                                                +"\n"+
										            "			ptr1[3] = ptr2[0];"                                                +"\n"+
										            "	    }"                                                               +"\n"+
										            "	}"                                                                   +"\n"+
										            "}"                                                                    +"\n"+
										            "}"                                                                    
										            ,
										            "gcc"
										            ,
										            "OK"
										            ,
										            },
/////////////////  45   ///////////////////	
										            {
										            "int foo_4_11() {"                                                     +"\n"+
										            "	char p[5];"                                                          +"\n"+
										            "	if (p[0] != 'a') ;"                                                  +"\n"+
										            "	return 0;"                                                           +"\n"+
										            "}"                                                                    
										            ,
										            "gcc"
										            ,
										            "UVF_P"
										            ,
										            },
/////////////////  46   ///////////////////	
										            {
										            "int bFontEqual(const char *szTable, int iBytesPerChar)"               +"\n"+
										            "{"                                                                    +"\n"+
										            "	const char	*pcTmp;"                                                  +"\n"+
										            ""                                                                     +"\n"+
										            "	for (pcTmp = szTable;*pucTmp != 0;pcTmp++) {"                        +"\n"+
										            "		break;"                                                             +"\n"+
										            "	}"                                                                   +"\n"+
										            "	return *pcTmp == '\\0';"                                              +"\n"+
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
