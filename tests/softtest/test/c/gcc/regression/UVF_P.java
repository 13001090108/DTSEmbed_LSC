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
				//总用例：34
					//未通过用例：1
					//未通过用例序号：6
////////////////////////////////  0   ////////////////////////////////////////	
		            {
		            "int test_uvf_p_1(){"                                                  +"\n"+
		            "    int *p;"                                                          +"\n"+
		            "    int a= *p;"                                        +"\n"+
		            "    return 0;"                                                        +"\n"+
		            "    }"                                                                
		            ,
		            "gcc"
		            ,
		            "UVF_P"
		            ,
		            },
////////////////////////////  1   ///////////////////////////////////////////
		            {
		            "void malloc(int *);"                                                  +"\n"+
		            "int test_uvf_p_1(){"                                                  +"\n"+
		            "    int *p=malloc(10);"                                               +"\n"+
		            "    int a=*p;//defect"                                                +"\n"+
		            "    return 0;"                                                        +"\n"+
		            "    }"                                                                
		            ,
		            "gcc"
		            ,
		            "UVF_P"
		            ,
		            },
//////////////////////////  2   ///////////////////	
		            {
		                "#include<stdio.h>"                                                  +"\n"+
		                "int test_uvf_p_2(){"                                                  +"\n"+
		                "    int *p;"                                                          +"\n"+
		                "    p=malloc(sizeof(int)*3);"                           +"\n"+
		                "    int a[3];"                                                        +"\n"+
		                "    a[1]=p[1];//defect,UVF_P,p"                          +"\n"+
		                "    return 0;"                                                        +"\n"+
		                "    }"                                                                
		                ,
		                "gcc"
		                ,
		                "UVF_P"
		                ,
		                },
///////////////////////////////  3   ///////////////////	
		                {
		                    "#include<string.h>"                                                   +"\n"+
		                    "#include<stdlib.h>"                                                   +"\n"+
		                    "#include<stdio.h>"                                                    +"\n"+
		                    "int test_uvf_p_3(){"                                                  +"\n"+
		                    "    char *s=malloc(sizeof(char)*6);"                     +"\n"+
		                    "    char *p=malloc(sizeof(char)*6);"                    +"\n"+
		                    "    strcpy(s,p);"                           +"\n"+
		                    "    return 0;"                                                        +"\n"+
		                    "    }"                                                                
		                    ,
		                "gcc"
		                ,
		                "UVF_P"
		                ,
		                },
///////////////////////////////  4   ///////////////////	
		                {
		                    "#include<string.h>"                                                   +"\n"+
		                    "#include<stdlib.h>"                                                   +"\n"+
		                    "#include<stdio.h>"                                                    +"\n"+
		                    "int test_uvf_p_3(){"                                                  +"\n"+
		                    "    char *s=malloc(sizeof(char)*6);"                     +"\n"+
		                    "    char *p=malloc(sizeof(char)*6);"                    +"\n"+
		                    "    p=\"123/0\";"                           +"\n"+
		                    "    strcpy(s,p);"                           +"\n"+
		                    "    return 0;"                                                        +"\n"+
		                    "    }"                                                                
		                    ,
		                "gcc"
		                ,
		                "OK"
		                ,
		                },		                
//////////////////////////////////5////////////////////
		                {
		                    "#include<stdlib.h>"                                                   +"\n"+
		                    "#include<stdio.h>"                                                    +"\n"+
		                    "int test_uvf_p_4(){"                                                  +"\n"+
		                    "    char *p;"                                                         +"\n"+
		                    "    p=malloc(sizeof(char)*1);"                    +"\n"+
		                    "    printf(\"%c\",p);//defect,uvf_p,p"            +"\n"+
		                    "    return 0;"                                                        +"\n"+
		                    "    }"                                                                
		                    ,
		                    "gcc"
		                    ,
		                    "OK"
		                    ,
		                },
/////////////////////////////////  6   ///////////////////	
		                {
		                "#include<string.h>"                                                   +"\n"+
			            "#include<stdlib.h>"                                                   +"\n"+
			            "#include<stdio.h>"                                                    +"\n"+
		                "int test_uvf_p_5(){"                                                  +"\n"+
		                "    char *p;"                                                         +"\n"+
		                "    p=malloc(sizeof(char)*2);"                    +"\n"+
		                "	scanf(\"%c\",p);"                                                      +"\n"+
		                "  printf(\"%c\",p[0]);"                                                  +"\n"+
		                "  return 0;"                                                        +"\n"+
		                "    }"                                                                
		                ,
		                "gcc"
		                ,
		                "OK"
		                ,
		                }, 
///////////////////////////////////////  7   ///////////////////	
		                {
		                "#include<stdio.h>"                                                    +"\n"+
		                "int test_uvf_p_5(int flag){"                                                  +"\n"+
		                "    char *p=(char*)malloc(10);"                                                         +"\n"+
		                "    if(0==flag){"                                                           +"\n"+
		                "          p[0]=1;    "                  +"\n"+
		                "    }"                                                                +"\n"+
		                "    return 0;"                                                        +"\n"+
		                "    }"                                                                
		                ,
		                "gcc"
		                ,
		                "OK"
		                ,
		                },
//////////////////////////////8///////////////////////////////////		                
			            {
		                	"#include<string.h>"                                                   +"\n"+
		                    "#include<stdlib.h>"                                                   +"\n"+
		                    "#include<stdio.h>"                                                    +"\n"+
				            "void fun()"                                                           +"\n"+
				            "{"                                                                    +"\n"+
				            "	char c[10],d[10];"                                                         +"\n"+				                                                               
				            "	sscanf(\"123456\",\"%s\",c);//FP"                                            +"\n"+
				            "	d=c;;"                                                        +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            
				            "OK"
				            ,
				            },
/////////////////  9 strcpy初始化 ///////////////////	
				             {
				            	"#include<string.h>"                                                   +"\n"+
			                    "#include<stdlib.h>"                                                   +"\n"+
			                    "#include<stdio.h>"                                                    +"\n"+	
			                    "void fun()"                                                           +"\n"+
			                    "{"                                                                    +"\n"+
			                    "char st1[6],st2[]=\"aaaaa\";"                                                  +"\n"+
			                    "strcpy(st1,st2);"                                                    +"\n"+
			                    "}" 
			                    ,
			                    "gcc"
			                    ,				            
			                    "OK"
			                    ,
				             },
/////////////////  10 strcpy初始化不合法 ///////////////////	
				             {
				            "#include<string.h>"                                                   +"\n"+
				            "#include<stdlib.h>"                                                   +"\n"+
				            "#include<stdio.h>"                                                    +"\n"+
				            "void fun()"                                                           +"\n"+
				            "{"                                                                    +"\n"+
				            "char* st1=(char*)malloc(10);" +"\n"+
				            "char* st2=(char*)malloc(10);"                                                  +"\n"+
				            "strcpy(st2,st1);"                 +"\n"+
				            "int i=st2[0];"                    +"\n"+
				            "}" 
				            ,
				            "gcc"
				            ,
				            "UVF_P"
				            ,
				            },
/////////////////  11 指针初始化///////////////////	
				    		
				            {
				            "fun()"                                                                +"\n"+
				            "{"                                                                    +"\n"+
				            "int a[5],*p;"                                                        +"\n"+
				            "p=a;"                                                                +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "OK"
				            ,
				            },
/////////////////  12 指针初始化///////////////////	
				    		
				            {
				            "fun()"                                                                +"\n"+
				            "{"                                                                    +"\n"+
				            "	int a[5],b[5];"                                                        +"\n"+
				            "	b=a;"                                                                +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "OK"
				            ,
				            },
/////////////////  13    数组初始化不合法///////////////////	
				    		
				            {
				            "fun()"                                                                +"\n"+
				            "{"                                                                    +"\n"+
				            "	int a[5];"                                                        +"\n"+
				            "	a[0]=a[1];//DEFECT,UVF_P,a"                                                                +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "UVF_P"
				            ,
				            },		
/////////////////  14   chh  数组初始化///////////////////	
				    		
				            {
				            "fun()"                                                              +"\n"+
				            "{"                                                                    +"\n"+
				            "	int a[5];"                                                       +"\n"+
				            "	a[0]=a[1]=0;"                                               +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "OK"
				            ,
				            },	
/////////////////  15  strcpy初始化 //////////////////
				            {
				            "void fun()"                                                           +"\n"+
				            "{"                                                                    +"\n"+
				            "char st1[5],st2[5];"                                                  +"\n"+
				            "strcmp(st1,st2);"                                                    +"\n"+
				            "}" 
				            ,
				            "gcc"
				            ,
				            
				            "OK"
				            ,
				            },	
////////////////  16switch初始化不可达   ///////////////////	
				            {
				            "void fun()"                                                           +"\n"+
				            "{"                                                                    +"\n"+
				            "int i;"                                                    +"\n"+
				            "int *a=(int *)malloc(sizeof*10);"                                                       +"\n"+
				            "int *b=(int *)malloc(sizeof*10);"                                                         +"\n"+
				            "i=0;"                                                                   +"\n"+
				            "switch(i)"                                                            +"\n"+
				            "{"                                                                    +"\n"+
				            "case 1:a[0]=2;break;"                                                    +"\n"+
				            "default:break;"                                                       +"\n"+
				            "}"                                                                    +"\n"+
				            "b=a;"                                                                 +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "OK"
				            ,
				            },
/////////////////  17 chh do_while 内先使用后初始化   ///////////////////	
				            {
				            "f()"                                                                  +"\n"+
				            "{"                                                                    +"\n"+
				            "int* a=(int *)malloc(sizeof*10);"                                                         +"\n"+
				            "do{a[0]=0;}while(1);"                +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "OK"
				            ,
				            },
/////////////////////////18/////////////////////
				            {
					            "int test_uvf_p_1(){"                                                  +"\n"+
					            "    int *p=(int *)malloc(sizeof*10);"                                                          +"\n"+
					            "    int *a=(int *)malloc(sizeof*10);"                                 +"\n"+
					            "    a[0]=1;"                                 +"\n"+
					            "    a=p;"                                                +"\n"+
					            "    return 0;"                                                        +"\n"+
					            "    }"                                                                
					            ,
					            "gcc"
					            ,
					            "OK"
					            ,
					            },	
////////////////////////////////19   ////////////////////////////////////////	
					            {
					            "#include<stdio.h>"                                                    +"\n"+
					            "int test_uvf_p_1(){"                                                  +"\n"+
					            "    int *p;"                                                          +"\n"+
					            "    p=malloc(sizeof(int )*3);"                            +"\n"+
					            "    int *a;"                                                        +"\n"+
					            "    a=p;"                                                +"\n"+				           
					            "    return 0;"                                                        +"\n"+
					            "    }"                                                                
					            ,
					            "gcc"
					            ,
					            "OK"
					            ,
					            },	
//////////////////////////////////20   ///////////////////	
					            {
					            "fun()"                                                                +"\n"+
					            "{"                                                                    +"\n"+
					            "	int a[5];"                                                           +"\n"+
					            "	a[0]=a[1]=a[3]=8;"                                        +"\n"+
					            ""                                                                     +"\n"+
					            "}"                                                                    
					            ,
					            "gcc"
					            ,
					            "OK"
					            ,
					            },	
/////////////////  21  ///////////////////	
					            {
					            "#include<string.h>"                                                   +"\n"+
					            "#include<stdlib.h>"                                                   +"\n"+
					            "#include<stdio.h>"                                                    +"\n"+
					            "int uvf_p_21(int i){"                                                          +"\n"+
					            "    char *p=(char *)malloc(sizeof(char)*4);"                          +"\n"+
					            "    char *a;"                                                         +"\n"+
					            "    if(i==1){"                                                           +"\n"+
					            "          a=p;"                                                       +"\n"+
					            "    }"                                                                +"\n"+
					            "    return 0;"                                                        +"\n"+
					            "    }"                                                                
					            ,
					            "gcc"
					            ,
					            "OK"
					            ,
					            },		
//////////////// 22   ///////////////////	
					            {
					            "#include<string.h>"                                                   +"\n"+
					            "#include<stdlib.h>"                                                   +"\n"+
					            "#include<stdio.h>"                                                    +"\n"+
					            "struct x{"                                                            +"\n"+
					            "       char y;"                                                       +"\n"+
					            "       };"                                                            +"\n"+
					            "int main(){"                                                          +"\n"+
					            " register   struct x *p=(struct x *)malloc(sizeof(struct x)*4);"              +"\n"+
					            "    struct x *a;"                                                     +"\n"+
					            "    if(1){"                                                           +"\n"+
					            "          a=p;"                                                       +"\n"+
					            "    }"                                                                +"\n"+
					            "//scanf(\"%c\",&(p->y));"                                             +"\n"+
					            "// printf(\"%c\",(p->y));"                                             +"\n"+
					            "//  system(\"pause\");"                                                 +"\n"+
					            "    return 0;"                                                        +"\n"+
					            "    }"                                                                
					            ,
					            "gcc"
					            ,
					            "OK"
					            ,
					            },		
/////////////////  23  ///////////////////	
					            {
					            "#include<string.h>"                                                   +"\n"+
					            "#include<stdlib.h>"                                                   +"\n"+
					            "#include<stdio.h>"                                                    +"\n"+
					            "char* uvf_p_23(int i){"                                                          +"\n"+
					            "    char *p=(char *)malloc(sizeof(char)*4);"                          +"\n"+
					            "    char *a;"                                                         +"\n"+
					            "    if(i==1){"                                                           +"\n"+
					            "          a[0]='A';"                                                       +"\n"+
					            "    }"                                                                +"\n"+
					            "    return a[0];"                                                        +"\n"+
					            "    }"                                                                
					            ,
					            "gcc"
					            ,
					            "OK"
					            ,
					            },		
/////////////////  24   ///////////////////	
					            {
					            "#include<string.h>"                                                   +"\n"+
					            "#include<stdlib.h>"                                                   +"\n"+
					            "#include<stdio.h>"                                                    +"\n"+
					            "int main(){"                                                          +"\n"+
					            "    char *p=\"abc\\0\";"                                                 +"\n"+
					            "    char *a;"                                                         +"\n"+
					            "    a=p;"                                                             +"\n"+
					            "    if(a[0]=='a'){"                                                   +"\n"+
					            "      printf(\"%d\",&a[2]);            "                                +"\n"+
					            "                  }"                                                  +"\n"+
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
					            "#include<stdlib.h>"                                                   +"\n"+
					            "#include<stdio.h>"                                                    +"\n"+
					            "int main(){"                                                          +"\n"+
					            "    char *p=\"abc\\0\";"                                                 +"\n"+
					            "    char *a;"                                                         +"\n"+
					            "    a=p;"                                                             +"\n"+
					            "    if(a[0]=='a'){"                                                   +"\n"+
					            "      printf(\"%c\",a[2]);            "                                +"\n"+
					            "                  }"                                                  +"\n"+
					            "    return 0;"                                                        +"\n"+
					            "    }"                                                                
					            ,
					            "gcc"
					            ,
					            "OK"
					            ,
					            },		
/////////////////  26   ///////////////////	
					            {
					            "#include<string.h>"                                                   +"\n"+
					            "#include<stdlib.h>"                                                   +"\n"+
					            "#include<stdio.h>"                                                    +"\n"+
					            "char ff(char *b){"                                                    +"\n"+
					            "    return b[0];"                                                     +"\n"+
					            "    }"                                                                +"\n"+
					            "int main(){"                                                          +"\n"+
					            "    char *p=\"abc\\0\";"                                                 +"\n"+
					            "    char c=ff(p);"                                                    +"\n"+
					            "    printf(\"%c\",c);"                                                  +"\n"+
					            "    return 0;"                                                        +"\n"+
					            "    }"                                                                
					            ,
					            "gcc"
					            ,
					            "OK"
					            ,
					            },						
/////////////////  27   ///////////////////	
					            {//过程间
					            "#include<string.h>"                                                   +"\n"+
					            "#include<stdlib.h>"                                                   +"\n"+
					            "#include<stdio.h>"                                                    +"\n"+
					            "char ff(char *b){"                                                    +"\n"+
					            "    return b[0];"                                                     +"\n"+
					            "    }"                                                                +"\n"+
					            "int main(){"                                                          +"\n"+
					            "    char *p=(char *)malloc(sizeof(char)*4);"                                                 +"\n"+
					            "    char c=ff(p);"                                                    +"\n"+
					            "    printf(\"%c\",c);"                                                  +"\n"+
					            "    return 0;"                                                        +"\n"+
					            "    }"                                                                
					            ,
					            "gcc"
					            ,
					            "UVF_P"
					            ,
					            },	
/////////////////  28   ///////////////////	
					            {//过程间
					            "#include<string.h>"                                                   +"\n"+
					            "#include<stdlib.h>"                                                   +"\n"+
					            "#include<stdio.h>"                                                    +"\n"+
					            "char ff(char *b){"                                                    +"\n"+
					            "     int i=1;"                                                        +"\n"+
					            "     char a;"                                                         +"\n"+
					            "     if(i==1){"                                                       +"\n"+
					            "      a=b[0];        "                                                +"\n"+
					            "      }    "                                                          +"\n"+
					            "    return a;"                                                        +"\n"+
					            "    }"                                                                +"\n"+
					            "int main(){"                                                          +"\n"+
					            "    char *p=(char *)malloc(sizeof(char)*4);//\"abc\\0\";"                +"\n"+
					            "    char c=ff(p);"                                                    +"\n"+
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
/////////////////////  29   ///////////////////	
					            {
					            "#include<string.h>"                                                   +"\n"+
					            "#include<stdlib.h>"                                                   +"\n"+
					            "#include<stdio.h>"                                                    +"\n"+
					            "char ff(char *b){"                                                    +"\n"+
					            "     int i=1;"                                                        +"\n"+
					            "     char a;"                                                         +"\n"+
					            "     if(i==1){"                                                       +"\n"+
					            "      a=b[0];        "                                                +"\n"+
					            "      }    "                                                          +"\n"+
					            "    return a;"                                                        +"\n"+
					            "    }"                                                                +"\n"+
					            "int main(){"                                                          +"\n"+
					            "    char *p=\"abc\\0\";"                +"\n"+
					            "    char c=ff(p);"                                                    +"\n"+
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
//////////////////////////////////30   ///////////////////	
					            {
					            "fun()"                                                                +"\n"+
					            "{"                                                                    +"\n"+
					            "	int a[5];"                                                           +"\n"+
					            "	a[0]=a[1]+8;"                                        +"\n"+
					            ""                                                                     +"\n"+
					            "}"                                                                    
					            ,
					            "gcc"
					            ,
					            "UVF_P"
					            ,
					            },		
/////////////////  31   ///////////////////	
					            {
					            "#include<string.h>"                                                   +"\n"+
					            "#include<stdlib.h>"                                                   +"\n"+
					            "#include<stdio.h>"                                                    +"\n"+
					            "char ff(char *b,char *c){"                                            +"\n"+
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
					            "    char c=ff(p,q);   //defect,UVF_P,q"                                  +"\n"+
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
/////////////////  32   ///////////////////	
					            {
					            "#include<string.h>"                                                   +"\n"+
					            "#include<stdlib.h>"                                                   +"\n"+
					            "#include<stdio.h>"                                                    +"\n"+
					            "char fff(char *w,char *y){"                                           +"\n"+
					            "     char x;"                                                         +"\n"+
					            "     if(w[1]>=y[1])"                                                  +"\n"+
					            "         x=w[1];"                                                     +"\n"+
					            "     else"                                                            +"\n"+
					            "         x=y[1];"                                                     +"\n"+
					            "     return x;"                                                       +"\n"+
					            "     }"                                                               +"\n"+
					            ""                                                                     +"\n"+
					            "char ff(char *b,char *c){"                                            +"\n"+
					            "     char a;"                                                         +"\n"+
					            "     a=fff(b,c);"                                                     +"\n"+
					            "     return a;    "                                                   +"\n"+
					            "    }"                                                                +"\n"+
					            "    "                                                                 +"\n"+
					            "int main(){"                                                          +"\n"+
					            "    char *q=(char *)malloc(sizeof(char)*4);"                          +"\n"+
					            "    char *p=\"abc\\0\";"                                                 +"\n"+
					            "    char c=ff(p,q);//defect,UVF_P,q"                                  +"\n"+
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
/////////////////  33   ///////////////////	
					            {
					            "#include<string.h>"                                                   +"\n"+
					            "#include<stdlib.h>"                                                   +"\n"+
					            "#include<stdio.h>"                                                    +"\n"+
					            "char fff(char *w,char *y){"                                           +"\n"+
					            "     char x;"                                                         +"\n"+
					            "     if(w[1]>=y[1])"                                                  +"\n"+
					            "         x=w[1];"                                                     +"\n"+
					            "     else"                                                            +"\n"+
					            "         x=y[1];"                                                     +"\n"+
					            "     return x;"                                                       +"\n"+
					            "     }"                                                               +"\n"+
					            ""                                                                     +"\n"+
					            "char ff(char *b,char *c){"                                            +"\n"+
					            "     char a;"                                                         +"\n"+
					            "     a=fff(b,c);"                                                     +"\n"+
					            "     return a;    "                                                   +"\n"+
					            "    }"                                                                +"\n"+
					            "    "                                                                 +"\n"+
					            "int main(){"                                                          +"\n"+
					            "    char *q=\"efg\\0\";"                          +"\n"+
					            "    char *p=\"abc\\0\";"                                                 +"\n"+
					            "    char c=ff(p,q);"                                  +"\n"+
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
/////////////////  34   ///////////////////	
					            {
					            "#include<string.h>"                                                   +"\n"+
					            "#include<stdlib.h>"                                                   +"\n"+
					            "#include<stdio.h>"                                                    +"\n"+
					            "char ff(char *b,char *c){"                                            +"\n"+
					            "     b[0]='a';"                                                    +"\n"+
					            "     c[0]='a';"                                                    +"\n"+
					            "     return c[0];    "                                               +"\n"+
					            "    }"                                                                +"\n"+
					            "int main(){"                                                          +"\n"+
					            "    char *q=(char *)malloc(sizeof(char)*4);"                          +"\n"+
					            "    char *p=(char *)malloc(sizeof(char)*4);"                                                 +"\n"+
					            "    char c=ff(p,q);"                                  +"\n"+
					            "    char d=q[0];"                                                  +"\n"+
					            "    char d=p[0];"                                                 +"\n"+
					            "    return 0;"                                                        +"\n"+
					            "    }"                                                                
					            ,
					            "gcc"
					            ,
					            "OK"
					            ,
					            },
		 });
	 }
}
