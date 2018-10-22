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
public class MLF extends ModelTestBase {
	public MLF(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/MLF-0.1.xml";
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
							"struct ghx_mlf_2_s2"                                                  +"\n"+
							"{"                                                                    +"\n"+
							"	char* ss;"                                                           +"\n"+
							""                                                                     +"\n"+
							"};"                                                                   +"\n"+
							"int ghx_mlf_2_f2()"                                                   +"\n"+
							"{"                                                                    +"\n"+
							"	struct ghx_mlf_2_s2 *s;"                                              +"\n"+
							"	s=(char*)malloc(10);"                                             +"\n"+
							//"	char* a=(char*)malloc(10);"                                          +"\n"+
							"	s->ss=*a;"                                                         +"\n"+
							"    return s;"                                                        +"\n"+
							"}//DEFECT"                                                            
							,
							"gcc"
							,
							"OK"
							,
				},

				//////////////////////////1//////////////////////////////////////////////
				{
					"#include \"stdlib.h\""                                                  +"\n"+
							"void ghx_mlf_3_f3()"                                                  +"\n"+
							"{"                                                                    +"\n"+
							"	int *m=NULL;"                                                        +"\n"+
							"	if((m=(int*)malloc(100))!=NULL)"                                     +"\n"+
							"	{"                                                                   +"\n"+
							"		return;//DEFECT"                                                    +"\n"+
							"	}"                                                                   +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"MLF"
							,
				},

				//////////////////////////2//////////////////////////////////////////////
				{
					"#include \"stdlib.h\""                                                  +"\n"+
							"void ghx_mlf_4_f4(int i)"                                             +"\n"+
							"{"                                                                    +"\n"+
							"	int a[5]={4,4,4,4,4,};"                                              +"\n"+
							"	int* m4=NULL;"                                                       +"\n"+
							"	if(i>0){"                                                            +"\n"+
							"		m4=a;"                                                              +"\n"+
							"	}else{"                                                              +"\n"+
							"		m4=(int*)malloc(100);"                                              +"\n"+
							"	}"                                                                   +"\n"+
							"	if(i>0)//DEFECT"                                                     +"\n"+
							"	{"                                                                   +"\n"+
							"		free(m4);"                                                          +"\n"+
							"	}"                                                                   +"\n"+
							"}"                                                                    +"\n"+
							"void ghx_mlf_4_f5(int i)"                                             +"\n"+
							"{"                                                                    +"\n"+
							"	int a[5]={4,4,4,4,4,};"                                              +"\n"+
							"	int* m4=NULL;"                                                       +"\n"+
							"	if(i>0){"                                                            +"\n"+
							"		m4=a;"                                                              +"\n"+
							"	}else{"                                                              +"\n"+
							"		m4=(int*)malloc(100);"                                              +"\n"+
							"	}"                                                                   +"\n"+
							"	if(i<0)//FP"                                                         +"\n"+
							"	{"                                                                   +"\n"+
							"		free(m4);"                                                          +"\n"+
							"	}"                                                                   +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"MLF"
							,
				},


				//////////////////////////3//////////////////////////////////////////////	
				{
					"#include <malloc.h>"                                                  +"\n"+
							"#include <stdio.h>"                                                   +"\n"+
							"#include <stdlib.h>"                                                  +"\n"+
							"void jhb_mlf_4_f1(unsigned int i)"                                    +"\n"+
							"{"                                                                    +"\n"+
							"char *p = (char*)malloc(12);"                                         +"\n"+
							"if(i>0) {"                                                            +"\n"+
							"free(p); "                                                            +"\n"+
							"}"                                                                    +"\n"+
							"return;   //FT"                                                       +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"MLF"
							,
				},


				//////////////////////////4//////////////////////////////////////////////
				{
					"void *malloc(int nmemb);"                                             +"\n"+
							"void free(void* p);"                                                  +"\n"+
							"void f2(){"                                                           +"\n"+
							"	int *memleak_error2=NULL;"                                           +"\n"+
							"	memleak_error2=(int*)malloc(sizeof(int)*100);"                       +"\n"+
							"	if(memleak_error2)return;//DEFECT, MLF, memleak_error2"              +"\n"+
							"	free(memleak_error2);"                                               +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"MLF"
							,
				},

				//////////////////////////5//////////////////////////////////////////////
				{
					"void *malloc(int nmemb);"                                             +"\n"+
							"void free(void* p);"                                                  +"\n"+
							"int *p;"                                                              +"\n"+
							"void f4(){"                                                           +"\n"+
							"	int *memleak_error5=NULL,*not_memleak_error5=NULL;"                  +"\n"+
							"	memleak_error5=(int*)malloc(100);"                                   +"\n"+
							"	not_memleak_error5=(int*)malloc(10);"                                +"\n"+
							"	p=not_memleak_error5; //assignment it to var that is global"         +"\n"+
							"}//DEFECT, MLF, memleak_error5"                                       
							,
							"gcc"
							,
							"MLF"
							,
				},
				//////////////////////////6//////////////////////////////////////////////
				{
					"void *malloc(int nmemb);"                                             +"\n"+
							"void free(void* p);"                                                  +"\n"+
							"int * f5(){"                                                          +"\n"+
							"	int *memleak_error6=(void*)0,*not_memleak_error6=(void*)0;"          +"\n"+
							"	memleak_error6=(int*)malloc(100);"                                   +"\n"+
							"	if(memleak_error6 != (void*)0){"                                     +"\n"+
							"		return (void*)0;//DEFECT, MLF, memleak_error6"                      +"\n"+
							"	}"                                                                   +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"MLF"
							,
				},
				//////////////////////////7//////////////////////////////////////////////
				{
					"void *malloc(int nmemb);"                                             +"\n"+
							"void free(void* p);"                                                  +"\n"+
							"void f6(){"                                                           +"\n"+
							"	int *memleak_error7=NULL;"                                           +"\n"+
							"	if((memleak_error7=(int*)malloc(100))==(void*)0){"                   +"\n"+
							"		return;//FP, MLF"                                                   +"\n"+
							"	}"                                                                   +"\n"+
							"	free(memleak_error7);"                                               +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				//////////////////////////8//////////////////////////////////////////////
				{
					"void *malloc(int nmemb);"                                             +"\n"+
							"void free(void* p);"                                                  +"\n"+
							"void f7(int i){"                                                      +"\n"+
							"	int a[5]={4,4,4,4,4,};"                                              +"\n"+
							"	int* melleak_error8=NULL,not_melleak_error8=NULL;"                   +"\n"+
							"	if(i>0){"                                                            +"\n"+
							"		melleak_error8=a;"                                                  +"\n"+
							"	}else{"                                                              +"\n"+
							"		melleak_error8=(int*)malloc(100);"                                  +"\n"+
							"	}"                                                                   +"\n"+
							"	if(i>0){"                                                            +"\n"+
							"		free(melleak_error8);"                                              +"\n"+
							"	}"                                                                   +"\n"+
							"}//DEFECT, MLF, melleak_error8"                                       
							,
							"gcc"
							,
							"MLF"
							,
				},
				//////////////////////////9//////////////////////////////////////////////
				{
					"void *malloc(int nmemb);"                                             +"\n"+
							"void free(void* p);"                                                  +"\n"+
							"void f8(){"                                                           +"\n"+
							"	int* melleak_error9=NULL;"                                           +"\n"+
							"	melleak_error9=(int*)malloc(100);"                                   +"\n"+
							"	melleak_error9++;//DEFECT, MLF, melleak_error9"                      +"\n"+
							"	free(melleak_error9);"                                               +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"MLF"
							,
				},
				//////////////////////////10//////////////////////////////////////////////
				{
					"void *malloc(int nmemb);"                                             +"\n"+
							"void free(void* p);"                                                  +"\n"+
							"void f9(){"                                                           +"\n"+
							"	int *q=NULL;"                                                        +"\n"+
							"	int*not_melleak_error10=NULL;"                                       +"\n"+
							"	not_melleak_error10=(int*)malloc(100);"                              +"\n"+
							"	q=not_melleak_error10;"                                              +"\n"+
							"	free(q);"                                                            +"\n"+
							"}//FP,MLF"                                                            
							,
							"gcc"
							,
							"OK"
							,
				},
				//////////////////////////11//////////////////////////////////////////////
				{
					"void *malloc(int nmemb);"                                             +"\n"+
							"void free(void* p);"                                                  +"\n"+
							"int func(int c)"                                                      +"\n"+
							"{"                                                                    +"\n"+
							"    char	*p;"                                                         +"\n"+
							""                                                                     +"\n"+
							"    if ((p = ((char *)malloc((sizeof (char) * 2)))) == 0)"            +"\n"+
							"			return 1;"                                                         +"\n"+
							"    free((char *)(p));"                                               +"\n"+
							"    return 1;//FP, MLF"                                               +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							" int"                                                                 +"\n"+
							"insert_char(int c)"                                                   +"\n"+
							"{"                                                                    +"\n"+
							"    int	*p;"                                                          +"\n"+
							" "                                                                    +"\n"+
							"    if ((p = ((int *)malloc((unsigned int)(sizeof (int) * (2))))) == ((void *)0))"+"\n"+
							"			return 1;"                                                         +"\n"+
							"    "                                                                 +"\n"+
							"    free((char *)(p));"                                               +"\n"+
							"    return 0;//FP, MLF"                                               +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				//////////////////////////12//////////////////////////////////////////////
				{
					"void *malloc(int nmemb);"                                             +"\n"+
							"void free(void* p);"                                                  +"\n"+
							"int func1(int c)"                                                     +"\n"+
							"{"                                                                    +"\n"+
							"    char	*p;"                                                         +"\n"+
							""                                                                     +"\n"+
							"		p = (char *)malloc(sizeof (char) * 2);"                             +"\n"+
							"    if (!p)"                                                          +"\n"+
							"			return 1;"                                                         +"\n"+
							"    free((char *)(p));"                                               +"\n"+
							"    return 1;"                                                        +"\n"+
							"}"                                                                    +"\n"+
							"int func2(int c)"                                                     +"\n"+
							"{"                                                                    +"\n"+
							"    char	*p;"                                                         +"\n"+
							""                                                                     +"\n"+
							"		p = (char *)malloc(sizeof (char) * 2);"                             +"\n"+
							"    if (p == (void*)0)"                                               +"\n"+
							"			return 1;"                                                         +"\n"+
							"		p = (void*)0;//DEFECT, MLF, p"                                      +"\n"+
							"    free((char *)(p));"                                               +"\n"+
							"    return 1;"                                                        +"\n"+
							"}"                                                                    +"\n"+
							"int func3(int c)"                                                     +"\n"+
							"{"                                                                    +"\n"+
							"    char	*p;"                                                         +"\n"+
							""                                                                     +"\n"+
							"		p = (char *)malloc(sizeof (char) * 2);"                             +"\n"+
							"    if (!p)"                                                          +"\n"+
							"			return 1;"                                                         +"\n"+
							"		p = (void*)0;//DEFECT, MLF, p"                                      +"\n"+
							"    free((char *)(p));"                                               +"\n"+
							"    return 1;"                                                        +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"MLF"
							,
				},

				//////////////////////////13//////////////////////////////////////////////
				{
					"void *malloc(int nmemb);"                                             +"\n"+
							"void free(void* p);"                                                  +"\n"+
							""                                                                     +"\n"+
							"void test1(){"                                                        +"\n"+
							"	int *ptr=(int*)malloc(sizeof(int)*100);"                             +"\n"+
							"	*ptr = 1;"                                                           +"\n"+
							"}//DEFECT, MLF, ptr"                                                  
							,
							"gcc"
							,
							"MLF"
							,
				},

				//////////////////////////14//////////////////////////////////////////////
				{
					//xwt:无法获得strdup函数声明，从scope中取得声明为空，怀疑是符号表的问题
					"#include <stdio.h>"                                                   +"\n"+
							"#include <stdlib.h>"                                                  +"\n"+
							"#include <string.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"void"                                                                 +"\n"+
							"test(char *str)"                                                      +"\n"+
							"{"                                                                    +"\n"+
							"	char *p;"                                                            +"\n"+
							""                                                                     +"\n"+
							"	p = strdup(str);"                                                    +"\n"+
							"	if(p) {"                                                             +"\n"+
							"		printf(\"result: %s\\n\", p);"                                         +"\n"+
							"		free(p);"                                                           +"\n"+
							"		free(p);			//DEFECT, MLF, p"                                        +"\n"+
							"	}"                                                                   +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int"                                                                  +"\n"+
							"main(int argc, char **argv)"                                          +"\n"+
							"{"                                                                    +"\n"+
							"	char *userstr;"                                                      +"\n"+
							""                                                                     +"\n"+
							"	if(argc > 1) {"                                                      +"\n"+
							"		userstr = argv[1];"                                                 +"\n"+
							"		test(userstr);"                                                     +"\n"+
							"	}"                                                                   +"\n"+
							"	return 0;"                                                           +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"MLF"
							,
				},
				//////////////////////////15//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"#include <string.h>"                                                  +"\n"+
							"#include <stdio.h>"                                                   +"\n"+
							""                                                                     +"\n"+
							"static char *GOT_LOCATION = (char *)0x0804c98c;"                      +"\n"+
							"static char shellcode[] = \"\\xeb\\x0cjump12chars_\\x90\\x90\\x90\\x90\\x90\\x90\\x90\\x90\"; //Robert is this right"+"\n"+
							""                                                                     +"\n"+
							"int main(void)"                                                       +"\n"+
							"{"                                                                    +"\n"+
							"	int size = sizeof(shellcode);"                                       +"\n"+
							"	void *shellcode_location;"                                           +"\n"+
							"	void *first, *second, *third, *fourth;"                              +"\n"+
							"	void *fifth, *sixth, *seventh;"                                      +"\n"+
							"	shellcode_location = (void *)malloc(size);"                          +"\n"+
							"	strcpy(shellcode_location, shellcode);"                              +"\n"+
							"	first = (void *)malloc(256);"                                        +"\n"+
							"	second = (void *)malloc(256);"                                       +"\n"+
							"	third = (void *)malloc(256);"                                        +"\n"+
							"	fourth = (void *)malloc(256);"                                       +"\n"+
							"	free(first);"                                                        +"\n"+
							"	free(third);"                                                        +"\n"+
							"	fifth = (void *)malloc(128);"                                        +"\n"+
							"	free(first);//DEFECT, MLF, first"                                    +"\n"+
							"	sixth = (void *)malloc(256);"                                        +"\n"+
							"	*((void **)(sixth+0))=(void *)(GOT_LOCATION-12);"                    +"\n"+
							"	*((void **)(sixth+4))=(void *)shellcode_location;"                   +"\n"+
							"	seventh = (void *)malloc(256);"                                      +"\n"+
							"	strcpy(fifth, \"something\");	"                                        +"\n"+
							"	return 0;//DEFECT, MLF, shellcode_location, second, sixth, fifth, fourth, seventh"+"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"MLF"
							,
				},
				//////////////////////////16//////////////////////////////////////////////
				//xwt:同14
				{
					""                                                                     +"\n"+
							"#include <stdio.h>"                                                   +"\n"+
							"#include <stdlib.h>"                                                  +"\n"+
							"#include <string.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"void test(char *str)"                                                 +"\n"+
							"{"                                                                    +"\n"+
							"	char *p;"                                                            +"\n"+
							""                                                                     +"\n"+
							"	p = strdup(str);"                                                    +"\n"+
							"	if(p)"                                                               +"\n"+
							"		printf(\"result: %s\\n\", p);"                                         +"\n"+
							""                                                                     +"\n"+
							"	return;//DEFECT, MLF, p"                                             +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int main(int argc, char **argv)"                                      +"\n"+
							"{"                                                                    +"\n"+
							"	char *userstr;"                                                      +"\n"+
							""                                                                     +"\n"+
							"	if(argc > 1) {"                                                      +"\n"+
							"		userstr = argv[1];"                                                 +"\n"+
							"		test(userstr);"                                                     +"\n"+
							"	}"                                                                   +"\n"+
							"	return 0;"                                                           +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"MLF"
							,
				},

				//////////////////////////17//////////////////////////////////////////////
				//JDH  需要修改
				//xwt:原本设想是：在使用了变量A作为参数调用free等函数释放动态内存的函数B中，若没有对A
				//进行全路径释放，则认为B没有释放A的函数特征，B不应该关联A
				//而实际情况是：实现生成函数特征是在状态机运转的之前，静态扫描的，无法处理路径敏感的
				//情况，若想处理，必须生成控制流图并遍历。这显然不可行,就目前而言，摘要的路径敏感处理
				//想不出可行方法
				//jdh: 需要考虑条件释放特征的建立  
				//jdh: 与zhb讨论p的区间, 由此提取特征 1

				{
					"#include <stdlib.h>"                                                  +"\n"+
							"  void my_free(char *p, int flag) {"                                  +"\n"+
							"      if (flag == 17) {"                                              +"\n"+
							"          p = 0;"                                                     +"\n"+
							"          return;  //DEFECT"                                          +"\n"+
							"      }"                                                              +"\n"+
							"      if (flag == 34) {"                                              +"\n"+
							"          return; //DEFECT"                                           +"\n"+
							"      }"                                                              +"\n"+
							"      free(p);"                                                       +"\n"+
							" }"																  +"\n"+
							"  void foo()"                                                      +"\n"+
							"  {"                                                                  +"\n"+
							"      int *ptr;"                                                      +"\n"+
							"      ptr = (int*)malloc(sizeof(int));"                               +"\n"+
							"      my_free(ptr,1); //DEFECT"                                            +"\n"+
							" }"                                                                   

		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
				},



				//////////////////////////18/////////////////////////////////////////////
				/*xwt：不识别全局变量*/
				//jdh  需要修改:添加状态转换条件  xwt

				{
					"#include <stdlib.h>"                                                  +"\n"+

		            "void f(int a){"                                                       +"\n"+
		            "   int * i;"                                                             +"\n"+
		            "   i=(int*)malloc(1);"                                                +"\n"+
		            "   i=(int*)malloc(1);//DEFECT"                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "MLF"
		            ,
				},

				//////////////////////////19//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"int * i;"                                                             +"\n"+
							"void f(int a){"                                                       +"\n"+
							"    i=(int*)malloc(1);"                                               +"\n"+
							"}"                                                                    +"\n"+
							"void f1(){"                                                           +"\n"+
							"   f();"                                                              +"\n"+
							"   i=(int*)malloc(1);//DEFECT"                                        +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"MLF"
							,
				},

				//////////////////////////20//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"void main()"                                                          +"\n"+
							"{"                                                                    +"\n"+
							"	int *ptr1, *ptr2, *tmp;"                                             +"\n"+
							"	int i;"                                                              +"\n"+
							""                                                                     +"\n"+
							"	ptr1 = (int *)malloc(sizeof(int));"                                  +"\n"+
							"	ptr2 = (int *)malloc(sizeof(int));"                                  +"\n"+
							""                                                                     +"\n"+
							"	for (i = 0; i < 3; i++) {"                                           +"\n"+
							"		tmp = ptr1;"                                                        +"\n"+
							"		ptr1 = ptr2;"                                                       +"\n"+
							"		ptr2 = tmp;"                                                        +"\n"+
							"	}"                                                                   +"\n"+
							""                                                                     +"\n"+
							"	free(ptr1);"                                                         +"\n"+
							"	free(ptr2); //FP"                                                    +"\n"+
							"	return;"                                                             +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"MLF"
							,
				},

				//////////////////////////21//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"int * i;"                                                             +"\n"+
							"void f(int* p,int flag){"                                             +"\n"+
							"      i=p;"                                                           +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void f1(int flag){"                                                   +"\n"+
							"   int*p =(int*)malloc(10);"                                          +"\n"+
							"   f(p,flag);"                                                        +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},

				//////////////////////////22//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"int * i;"                                                             +"\n"+
							"void f(int* p,int flag){"                                             +"\n"+
							"   if(flag)"                                                          +"\n"+
							"      i=p;"                                                           +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void f1(int flag){"                                                   +"\n"+
							"   int*p =(int*)malloc(10);"                                          +"\n"+
							"   f(p,flag);"                                                        +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},

				//////////////////////////23//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"int * i;"                                                             +"\n"+
							"void f(int* p,int flag){"                                             +"\n"+
							"   if(flag)"                                                          +"\n"+
							"      free(p);"                                                       +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void f1(int flag){"                                                   +"\n"+
							"   int*p =(int*)malloc(10);"                                          +"\n"+
							"   f(p,flag);"                                                        +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"MLF"
							,
				},


				//////////////////////////24//////////////////////////////////////////////
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
							"MLF"
							,
				},

				//////////////////////////25//////////////////////////////////////////////
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
							"MLF"
							,
				},



				//////////////////////////26//////////////////////////////////////////////

				{
					"#include <stdlib.h>"                                                  +"\n"+
							"  void my_free(char *p, int flag) {"                                  +"\n"+
							"      if (flag == 17) {"                                              +"\n"+
							"          p = 0;"                                                     +"\n"+
							"          return;  //DEFECT"                                          +"\n"+
							"      }"                                                              +"\n"+
							"      if (flag == 34) {"                                              +"\n"+
							"          return; //DEFECT"                                           +"\n"+
							"      }"                                                              +"\n"+
							"      free(p);"                                                       +"\n"+
							" }"                                                                   
							,
							"gcc"
							,
							"OK"
							,
				},



				////////////////////////  27  ///////////////////////////////////////////	
				{
					"#include <stdio.h>"                                                   +"\n"+
							"#include <stdlib.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"typedef struct {"                                                     +"\n"+
							"   char a[12];"                                                       +"\n"+
							"   char b[34];"                                                       +"\n"+
							"   int i;"                                                            +"\n"+
							"   char *p;"                                                          +"\n"+
							"}S;"                                                                  +"\n"+
							"S  s;"                                                                +"\n"+
							"char* f(){"                                                           +"\n"+
							"   "                                                                  +"\n"+
							"   s.p=(char*)malloc(10);"                                            +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void f1(){"                                                           +"\n"+
							"   f();"                                                              +"\n"+
							"   s.p=(char*)malloc(10);"                                            +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"MLF"
							,
				},
				////////////////////////  28  ///////////////////////////////////////////	
				{
					"#include <stdio.h>"                                                   +"\n"+
							"#include <stdlib.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"typedef struct {"                                                     +"\n"+
							"   char a[12];"                                                       +"\n"+
							"   char b[34];"                                                       +"\n"+
							"   int i;"                                                            +"\n"+
							"   char *p;"                                                          +"\n"+
							"}S;"                                                                  +"\n"+
							"S  s;"                                                                +"\n"+
							""                                                                     +"\n"+
							"void f1(){"                                                           +"\n"+
							"   s.p=(char*)malloc(10);"                                                              +"\n"+
							"   s.p=(char*)malloc(10);"                                            +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"MLF"
							,
				},
				//////////////////////////29//////////////////////////////////////////////
				{
					"  #include <stdio.h>"                                                 +"\n"+
							"  #include <stdlib.h>"                                                 +"\n"+
							"  "                                                                   +"\n"+
							"  int * my_open_r(int a) {"                               +"\n"+
							"      int *pf = (int *)malloc(a);"                                  +"\n"+
							"      return pf;"                                                      +"\n"+
							" }"                                                                   +"\n"+
							" "                                                                    +"\n"+
							" int test_file(const int s) {"                                   +"\n"+
							"     int *dummy;"                                                    +"\n"+
							"     dummy = my_open_r(s);"                                         +"\n"+
							"     return 1; //DEFECT"                                              +"\n"+
							" }"                                                                   
							,
							"gcc"
							,
							"MLF"
							,
				},
				//////////////////////////30//////////////////////////////////////////////
				{
					"  #include <stdio.h>"                                                 +"\n"+
							"  #include <stdlib.h>"                                                 +"\n"+
							"  "                                                                   +"\n"+
							"  int  my_open_r(int a,int **pf) {"                               +"\n"+
							"      *pf = (int *)malloc(a);"                                  +"\n"+
							"      return 1;"                                                      +"\n"+
							" }"                                                                   +"\n"+
							" "                                                                    +"\n"+
							" int test_file(const int s) {"                                   +"\n"+
							"     int *dummy;"                                                    +"\n"+
							"     int i = my_open_r(s,&dummy);"                                         +"\n"+
							"     return i; //DEFECT"                                              +"\n"+
							" }"                                                                   
							,
							"gcc"
							,
							"OK"
							,
				},
                 /////////////////  0   ///////////////////	
	            {
	            "#include<stdlib.h>"                                                   +"\n"+
	            "void func1(int *p){"                                                  +"\n"+
	            "    free(p);     "                                                    +"\n"+
	            "}"                                                                    +"\n"+
	            "void func2(){"                                                        +"\n"+
	            "    int * p = (int *)malloc(10);"                                     +"\n"+
	            "    func1(p);"                                                        +"\n"+
	            "}"                                                                    
	            ,
				"gcc"
				,
				"OK"
				,
	            },
				//////////////////////////1//////////////////////////////////////////////
				{
					"#include \"stdlib.h\""                                                  +"\n"+
							"void ghx_mlf_3_f3()"                                                  +"\n"+
							"{"                                                                    +"\n"+
							"	int *m=(int*)malloc(100);"                                                        +"\n"+
							"	if(m)"                                                          +"\n"+
							"	{"                                                                   +"\n"+
							"		free(m);//DEFECT"                                            +"\n"+
							"	}"                                                                   +"\n"+
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
