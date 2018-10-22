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
public class UVF extends ModelTestBase {
	public UVF(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/UVF-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("fault");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);

		//加载库函数摘要
		Set<MethodNameDeclaration> libDecls = libManager.compileLib(pre.getLibIncludes());
		interContext = InterContext.getInstance();
		interContext.addLibMethodDecl(libDecls);
	}
	@Parameters
	public static Collection<Object[]> testcaseAndResults()
	{
		return Arrays.asList(new Object[][] {
				//总用例：69
				//未通过用例：2
				//未通过用例序号:2,29

				//////////////////////////0//////////////////////////////////////////////
				{
					"#include <stdio.h>"                                                   +"\n"+
							"int ghx_uvf_1_f1(int a)"                                              +"\n"+
							"{"                                                                    +"\n"+
							"	int b;"                                                              +"\n"+
							"switch(a)"                                                            +"\n"+
							"{"                                                                    +"\n"+
							"case 1:"                                                              +"\n"+
							"	b=1;"                                                                +"\n"+
							"case 2:"                                                              +"\n"+
							"	b=2;"                                                                +"\n"+
							"case 3:"                                                              +"\n"+
							"	b=3;"                                                                +"\n"+
							"}"                                                                    +"\n"+
							"b++;//DEFECT"                                                         +"\n"+
							"return 0;"                                                            +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"UVF"
							,
				},
				//////////////////////////1//////////////////////////////////////////////
				{//
					"wsprintf(char* Buffer,int  b,int number);//#include <windows.h>"                                                 +"\n"+
							"void ghx_uvf_10_f10()"                                                +"\n"+
							"{"                                                                    +"\n"+
							"char Buffer[100]; "                                                   +"\n"+
							"int number=100; "                                                     +"\n"+
							"wsprintf(Buffer, \"%d\",number); //FP"                                  +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				//////////////////////////2//////////////////////////////////////////////
				{//测试用例编译不能通过，不能识别va_list
					//windows.h该头展开后为什么会溢出，原因有待查明！！！！noted by zhouhb
					"#include <stdio.h>"          +"\n"+
					"#include<stdarg.h>"          +"\n"+
							"//#include <windows.h>"                                                 +"\n"+
							"int vspf(int size,char *fmt,...)"                                     +"\n"+
							"{"                                                                    +"\n"+
							"    char buf[10];     "                                               +"\n"+
							"	int cnt=0;"                                                          +"\n"+
							"    va_list arg;"                                                     +"\n"+
							"    va_start(arg,fmt);"                                               +"\n"+
							"    cnt = _vsnprintf(buf,size,fmt,arg);//FP"                          +"\n"+
							"    va_end(arg);"                                                     +"\n"+
							"    return cnt;"                                                      +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				//////////////////////////3//////////////////////////////////////////////
				{//4,zl, 
					//测试用例头文件加载不全
					//模式中之前没有处理 fprintf函数的能力
					"#include <stdio.h>"                                                   +"\n"+
					"//#include <process.h>"                                                 +"\n"+
					"#include<string.h>"                                                   +"\n"+
					"void ghx_uvf_12_f12( void )"                                          +"\n"+
					"{"                                                                    +"\n"+
					"   FILE *stream;"                                                     +"\n"+
					"   int    i = 10;"                                                    +"\n"+
					"   char   s1[10];"                                                    +"\n"+
					"   char   s2[]=\"welcome to beijing\";"                                 +"\n"+
					"   char   c = '\\n';"                                                  +"\n"+
					""                                                                     +"\n"+
					"   stream = fopen( \"fprintf.out\", \"w\" );"                             +"\n"+
					"   fprintf( stream, \"%s%c\", s1, c );//DEFECT"                         +"\n"+
					"   fprintf( stream, \"%s%c\", s2, c );//FP"                             +"\n"+
					"   fprintf( stream, \"%d\\n\", i );//FP"                                 +"\n"+
					"   fclose( stream );"                                                 +"\n"+
					"}"                                                             
					,
					"gcc"
					,
					"UVF"
					,
				},
				//////////////////////////4//////////////////////////////////////////////
				{
					"void ghx_uvf_2_f2(int b)"                                             +"\n"+
							"{"                                                                    +"\n"+
							"	int a;"                                                              +"\n"+
							" if(b)"                                                               +"\n"+
							" {"                                                                   +"\n"+
							"	 a=1;"                                                               +"\n"+
							" }"                                                                   +"\n"+
							" else"                                                                +"\n"+
							" { "                                                                  +"\n"+
							"	 a=2;"                                                               +"\n"+
							" }"                                                                   +"\n"+
							"a++;//FP"                                                             +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				//////////////////////////5/////////////////////////////////////////////
				{
					"#include <stdio.h>"                                                   +"\n"+
							"int ghx_uvf_4_f4 (int a)"                                             +"\n"+
							"{"                                                                    +"\n"+
							"  char buffer [50];"                                                  +"\n"+
							"  int n;"                                                             +"\n"+
							"  n=sprintf (buffer, \"%d \", a);//FP"                                  +"\n"+
							"  return 0;"                                                          +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				//////////////////////////6////////////////////////////////////////	
				{
					"#include <string.h>"                                                  +"\n"+
							"int ghx_uvf_3_f3 ()"                                                  +"\n"+
							"{"                                                                    +"\n"+
							"  char str[20];"                                                      +"\n"+
							"  memset (str,'-',6);//DEFECT"                                        +"\n"+
							"  return 0;"                                                          +"\n"+
							"}"                                                                    +"\n"+
							"int ghx_uvf_3_f4 ()"                                                  +"\n"+
							"{"                                                                    +"\n"+
							"  char str[]=\"welcome to beijing\";"                                   +"\n"+
							"  memset (str,'-',6);//FP"                                            +"\n"+
							"  return 0;"                                                          +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				///////////////////////////////////7////////////////////////////////////
				{//过程间
					"void ff(int *b){"                                                     +"\n"+
					"     b++;"                                                            +"\n"+
					"     return ;"                                                        +"\n"+
					"     }"                                                               +"\n"+
					"int aa(){"                                                            +"\n"+
					"    int *a;"                                                          +"\n"+
					"    ff(a);//defect"                                                           +"\n"+
					"    return 0;"                                                        +"\n"+
					"    } "                                                               
					,
					"gcc"
					,
					"OK"
					,
				},
				//////////////////////////8//////////////////////////////////////////////
				{
					"#include <stdio.h>"                                                   +"\n"+
							"int ghx_uvf_5_f5()"                                                   +"\n"+
							"{"                                                                    +"\n"+
							"   FILE * pFile;"                                                     +"\n"+
							"   char string [100];"                                                +"\n"+
							""                                                                     +"\n"+
							"   pFile = fopen (\"myfile.txt\" , \"r\");"                               +"\n"+
							"   if (pFile == NULL) perror (\"Error opening file\");"                 +"\n"+
							"   else {"                                                            +"\n"+
							"     fgets (string , 100 , pFile);//FP"                               +"\n"+
							"     puts (string);"                                                  +"\n"+
							"     fclose (pFile);"                                                 +"\n"+
							"   }"                                                                 +"\n"+
							"   return 0;"                                                         +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				//////////////////////////9//////////////////////////////////////////////
				{
					"#include <string.h>"                                                  +"\n"+
							"#include <stdio.h>"                                                   +"\n"+
							"int ghx_uvf_6_f6()"                                                   +"\n"+
							"{"                                                                    +"\n"+
							"FILE *stream;"                                                        +"\n"+
							"char msg[] = \"this is a test\";"                                       +"\n"+
							"char buf[20];"                                                        +"\n"+
							"stream = fopen(\"DUMMY.FIL\", \"w+\");"                                   +"\n"+
							""                                                                     +"\n"+
							"if(stream)"                                                           +"\n"+
							"{"                                                                    +"\n"+
							"fread(buf, strlen(msg)+1, 1,stream);//FP"                             +"\n"+
							""                                                                     +"\n"+
							"fclose(stream);"                                                      +"\n"+
							"}"                                                                    +"\n"+
							"return 0;"                                                            +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				//////////////////////////10//////////////////////////////////////////////	
				{
					"#include <stdlib.h>"                                                  +"\n"+
							"void ghx_uvf_7_f7(  )"                                                +"\n"+
							"{"                                                                    +"\n"+
							"   char buffer[20];"                                                  +"\n"+
							"   int  i = 3000;"                                                    +"\n"+
							"   _itoa( i, buffer, 10 );  //FP"                                     +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				//////////////////////////11//////////////////////////////////////////////
				{
					"#include <stdio.h> "                                                  +"\n"+
							"#include <string.h>"                                                  +"\n"+
							"void ghx_uvf_9_f9()"                                                  +"\n"+
							"{"                                                                    +"\n"+
							"char array[30];"                                                      +"\n"+
							"char *name = \"gonghongxia\";"                                          +"\n"+
							"_snprintf(array, strlen(array), \"%s\", name);//FP"                     +"\n"+
							"}int main() {return 0;}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				
				//////////////////////////12//////////////////////////////////////////////
				{
					"#include <stdio.h>"                                                   +"\n"+
							"#include <string.h>"                                                  +"\n"+
							"void jhb_uvf_1_f1(int *nLines,char sName[]){"                         +"\n"+
							"	int nNameNo=32;"                                                     +"\n"+
							"	char sOldName[128];"                                                 +"\n"+
							"	if ((*nLines)>=10)"                                                  +"\n"+
							"	{"                                                                   +"\n"+
							"		while (nNameNo)"                                                    +"\n"+
							"		{"                                                                  +"\n"+
							"			strcpy(sOldName,sName);   //FP"                                    +"\n"+
							"		}"                                                                  +"\n"+
							"	//	unlink(sOldName); 未声明该函数"                                         +"\n"+
							"	}"                                                                   +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				//////////////////////////13//////////////////////////////////////////////
				{
					"void f2(){"                                                           +"\n"+
							"   int i;"                                                            +"\n"+
							"   f1(i);//"                                                          +"\n"+
							"}"                                                                    +"\n"+
							"void f1(int i){"                                                      +"\n"+
							"   f(i);"                                                             +"\n"+
							"}"                                                                    +"\n"+
							"void f(int i){"                                                       +"\n"+
							"   int j=i;"                                                          +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"UVF"
							,
				},
				//////////////////////////14//////////////////////////////////////////////
				{
					"#include <string.h>  "                                                +"\n"+
							"int main()"                                                           +"\n"+
							"  {"                                                                  +"\n"+
							"  	char FIXEDbuf[12];"                                                +"\n"+
							"  	char *POINTERbuf;"                                                 +"\n"+
							"  	strcpy(FIXEDbuf, \"Something rather large\");  "                     +"\n"+
							"    strcpy(FIXEDbuf, \"123456789012\");  "                              +"\n"+
							"    strcpy(FIXEDbuf, \"12345678901\");  "                               +"\n"+
							"  	strcpy(POINTERbuf, \"Something very large as well\"); //DEFECT"      +"\n"+
							"  "                                                                   +"\n"+
							"  	return 0;"                                                         +"\n"+
							"  }"                                                                  
							,
							"gcc"
							,
							"OK"
							,
				},
				
				/////////////////////////15/////////////////////////////////////////////
				{//测试用例编译不能通过，不能识别FILE
					"#include <string.h>"                                                  +"\n"+
					"#include <stdio.h>"                                                   +"\n"+
							"fun(FILE* str){"                                                      +"\n"+
							"	char buffer[11];"                                                    +"\n"+
							"    fgets(buffer,10, str);"                                           +"\n"+
							"	printf(\"%s\",buffer);"                                                +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////////////16/////////////////////////////////////////////
				{
					"#include <string.h>"                                                  +"\n"+
							"#include <stdio.h>"                                                   +"\n"+
							"fun(char* str){"                                                      +"\n"+
							"	char buffer[11];"                                                    +"\n"+
							"	strcpy(str, buffer); //DEFECT"                                       +"\n"+
							"    strcpy(buffer, str);"                                             +"\n"+
							"	printf(\"%s\",buffer);"                                                +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"UVF"
							,
				},
				/////////////////////////17/////////////////////////////////////////////
				{//测试用例编译不能通过，不能识别FILE
					"#include <string.h>"                                                  +"\n"+
							"#include <stdio.h>"                                                   +"\n"+
							"fun(FILE* str){"                                                      +"\n"+
							"	char buffer[11];"                                                    +"\n"+
							"    scanf(\"%s\",buffer);//FP"                                      +"\n"+
							"	printf(\"%s\",buffer);"                                                +"\n"+
							"}int main() {return 0;}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				
				
				/////////////////////////18/////////////////////////////////////////////
				{
					"#include <string.h>"                                                  +"\n"+
					"#include <stdio.h>"                                                   +"\n"+
					""                                                                     +"\n"+
					"f1(int *a,int *b, char* s){"                                          +"\n"+
					"	char a1=*s; "                                                +"\n"+
					"	"                                                                    +"\n"+
					"}"                                                                    +"\n"+
					"main(){"                                                              +"\n"+
					"	char a[3];"                                                          +"\n"+
					"	int b,c,d;"                                                          +"\n"+
					"	f1(0,0,a);"                                                          +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"OK"
					,
				},
/////////////////////////19/////////////////////////////////////////////
				{
					"void test3(int i) "                                                   +"\n"+
					"{"                                                                    +"\n"+
					"	int c;"                                                              +"\n"+
					"	switch(i){"                                                          +"\n"+
					"	case 1:"                                                             +"\n"+
					"	default:"                                                            +"\n"+
					"		c=1;"                                                               +"\n"+
					"		break;"                                                             +"\n"+
					"	case 2:"                                                             +"\n"+
					"		c=2;"                                                               +"\n"+
					"		break;"                                                             +"\n"+
					"	case 3:"                                                             +"\n"+
					"		break;"                                                             +"\n"+
					"	}"                                                                   +"\n"+
					"  c++;   //DEFECT,UVF,c"                                              +"\n"+
					"}"        
					,
					"gcc"
					,
					"UVF"
					,  
				},
/////////////////////////20/////////////////////////////////////////////
				{
					"int p;"                                                               +"\n"+
							"fun(){"                                                               +"\n"+
							"	p=0;"                                                                +"\n"+
							"}"                                                                    +"\n"+
							"f1(){"                                                                +"\n"+
							"	fun();"                                                              +"\n"+
							"	int x=p;"                                                            +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
////////////////////////21/////////////////////////////////////////////
				{
					"main(){"                                                              +"\n"+
							""                                                                     +"\n"+
							"	char a[12];"                                                         +"\n"+
							"	char* p=a; //FP"                                                     +"\n"+
							"	char *b;"                                                            +"\n"+
							"	p=b;  //DEFECT"                                                      +"\n"+
							""                                                                     +"\n"+
							""                                                                     +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"UVF"
							,
				},
				
/////////////////////////22/////////////////////////////////////////////
				{
					"f(){"                                                                 +"\n"+
							"  int i=10,j;"                                                        +"\n"+
							"  while(i--){"                                                        +"\n"+
							"     j=1;"                                                            +"\n"+
							"  }"                                                                  +"\n"+
							"  i=j;"                                                               +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
/////////////////////////23/////////////////////////////////////////////
				{
					"#include <stdio.h>"                                                   +"\n"+
							""                                                                     +"\n"+
							"void f()"                                                             +"\n"+
							"{"                                                                    +"\n"+
							"    char buf[256];"                                                   +"\n"+
							""                                                                     +"\n"+
							"    fgets(buf, sizeof(buf), stdin);"                                  +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
////////////////////////24/////////////////////////////////////////////
				{
					"#include <stdio.h>"                                                 +"\n"+
							"#include <string.h>"                                                  +"\n"+
							"f(){"                                                                 +"\n"+
							"   char name[12],name1[12];"                                          +"\n"+
							"   strcpy(name1,name);"                                               +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"UVF"
							,
				},
/////////////////////////25/////////////////////////////////////////////
				{
					""                                                                     +"\n"+
							"void f2(int f){"                                                      +"\n"+
							"	int p=f;"                                                            +"\n"+
							"}"                                                                    +"\n"+
							"void f1(int f){"                                                      +"\n"+
							"	f2(f);"                                                              +"\n"+
							""                                                                     +"\n"+
							"}"                                                                    +"\n"+
							"main(){"                                                              +"\n"+
							"    int flag;"                                                        +"\n"+
							"	f1(flag); //DEFECT"                                                  +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"UVF"
							,
				},
/////////////////////////26/////////////////////////////////////////////
				{
					"#include <stdio.h>"                                                   +"\n"+
							""                                                                     +"\n"+
							"f()"                                                                  +"\n"+
							"{"                                                                    +"\n"+
							"    char buf[256];"                                                   +"\n"+
							""                                                                     +"\n"+
							"    fgets(buf, sizeof(buf), stdin);"                                  +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
/////////////////////////27/////////////////////////////////////////////
				{
					"void test4(int i) "                                                   +"\n"+
					"{"                                                                    +"\n"+
					"	int c;"                                                              +"\n"+
					"	switch(i){"                                                          +"\n"+
					"	case 1:"                                                             +"\n"+
					"		c=1;"                                                               +"\n"+
					"		break;"                                                             +"\n"+
					"	case 2:"                                                             +"\n"+
					"		c=2;"                                                               +"\n"+
					"		break;"                                                             +"\n"+
					"	}"                                                                   +"\n"+
					"  c++; //DEFECT,UVF,c"                                                +"\n"+
					"}"          
					,
					"gcc"
					,
					"UVF"
					,  
				},				
/////////////////////////28/////////////////////////////////////////////
				{
					""                                                                     +"\n"+
							""                                                                     +"\n"+
							"void func()"                                                          +"\n"+
							"{"                                                                    +"\n"+
							"	int buf[5];"                                                         +"\n"+
							"	int *ptr = buf;"                                                     +"\n"+
							""                                                                     +"\n"+
							"	if (ptr != buf + sizeof(buf)) //FP"                                  +"\n"+
							"		return;"                                                            +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"UVF"
							,
				},
/////////////////////////29/////////////////////////////////////////////
				{//只有这三个取值，所以不可能出现其他的路径，无法解决
					//jdh  需要修改控制流生成   zhb
					"enum days {MONDAY, TUESDAY, SUNDAY};"                                 +"\n"+
					""                                                                     +"\n"+
					"int func(enum days var)"                                                   +"\n"+
					"{"                                                                    +"\n"+
					"	int tmp;"                                                            +"\n"+
					""                                                                     +"\n"+
					"	switch(var) {"                                                       +"\n"+
					"	case MONDAY:"                                                        +"\n"+
					"		tmp = 1;"                                                           +"\n"+
					"	case TUESDAY:"                                                       +"\n"+
					"		tmp = 2;"                                                           +"\n"+
					"	case SUNDAY:"                                                        +"\n"+
					"		tmp = 7;"                                                           +"\n"+
					"	};"                                                                  +"\n"+
					""                                                                     +"\n"+
					"	return tmp; //FP"                                                    +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"OK"
					,
				},
/////////////////////////30/////////////////////////////////////////////
				{//循环处理，数组耽搁成员变量的初始化识别，目前都无法处理，zl，20110926
					"  "                                                                   +"\n"+
					"  void uninit_array_might(int s) {"                                   +"\n"+
					"      int a[10];"                                                     +"\n"+
					"      if (s) {"                                                       +"\n"+
					"          int i;"                                                     +"\n"+
					"          for(i = 0; i < 10; i++) {"                                  +"\n"+
					"              a[i] = 0;"                                              +"\n"+
					"         }"                                                           +"\n"+
					"     }"                                                               +"\n"+
					"     int i=a[4]; //DEFECT"                                            +"\n"+
					" }"                                                                   
					,
					"gcc"
					,
					"UVF"
					,
				},
/////////////////////////31/////////////////////////////////////////////
				{
					"  int incomplete_init() {"                                            +"\n"+
							"      int a[10];"                                                     +"\n"+
							"      int i;"                                                         +"\n"+
							"      for (i = 9; i > 0; i--) {"                                      +"\n"+
							"          a[i] = i;"                                                  +"\n"+
							"      }"                                                              +"\n"+
							"      return a[0]; //DEFECT"                                          +"\n"+
							"  }"                                                                  
							,
							"gcc"
							,
							"OK"
							,
				},
/////////////////////////32/////////////////////////////////////////////
				{
							"  void uninit_array_must() {"                                         +"\n"+
							"      int a[10];"                                                     +"\n"+
							"      int i=a[1]; //DEFECT"                                           +"\n"+
							"  }"                                                                  
							,
							"gcc"
							,
							"UVF"
							,
				},
/////////////////////////33/////////////////////////////////////////////
				{
					"int a;"                                                               +"\n"+
					"int func3(){"                                                                    +"\n"+
					"	int b;"                                                              +"\n"+
					"	b = a;  //FP,UVF"                                                    +"\n"+
					"}"        
					,
					"gcc"
					,
					"OK"
					,                       
				},			
/////////////////////////34/////////////////////////////////////////////	
				{
					"#include <stdio.h>"                                                   +"\n"+
							"#include <string.h>"                                                  +"\n"+
							"void jhb_uvf_1_f1(int *nLines,char sName[]){"                         +"\n"+
							"	int nNameNo=32;"                                                     +"\n"+
							"	char sOldName[128];"                                                 +"\n"+
							"	if ((*nLines)>=10)"                                                  +"\n"+
							"	{"                                                                   +"\n"+
							"		while (nNameNo)"                                                    +"\n"+
							"		{"                                                                  +"\n"+
							"			strcpy(sOldName,sName);   //DEFECT"                                +"\n"+
							"		}"                                                                  +"\n"+
							"	//	unlink(sOldName);"                                                +"\n"+
							"	}"                                                                   +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				
/////////////////////////35/////////////////////////////////////////////
				{//对time的一些函数添加了处理模块,zl
					"#include <time.h>"                                                    +"\n"+
					""                                                                     +"\n"+
					"void f_UVF_1()"                                                       +"\n"+
					"{"                                                                    +"\n"+
					"	char current[128];"                                                  +"\n"+
					"	"                                                                    +"\n"+
					"	_strdate(current); //UVF,current,false alarm"                        +"\n"+
					"	return;"                                                             +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"OK"
					,
				},
/////////////////////////36/////////////////////////////////////////////
				{//测试用例不能通过编译，FILE不能识别
					"#include <stdio.h>"                                                   +"\n"+
							""                                                                     +"\n"+
							"void zk_uvf_10_f1(FILE *fp)"                                          +"\n"+
							"{"                                                                    +"\n"+
							"	int buf[10];"                                                        +"\n"+
							""                                                                     +"\n"+
							"	fread(buf, 1, 10, fp); //fp"                                         +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
/////////////////////////////////////////////37///////////////////////
				{
					"#include<stdio.h> "                                                   +"\n"+
					"static int outfile(char *filename)"                                   +"\n"+
					"{"                                                                    +"\n"+
					"   FILE *f = fopen(filename, \"wb\");"             +"\n"+
					"   if (f) {"                                                          +"\n"+
					"      "                                                               +"\n"+
					"      fclose(f);"                                                     +"\n"+
					"   }"                                                                 +"\n"+
					"   return f != NULL; //FP,UVF"                                        +"\n"+
					"}"     
				,
				"gcc"
				,
				"OK"
				,  
				},
/////////////////////////38/////////////////////////////////////////////
				{
					"#include <stdio.h>"                                                   +"\n"+
							""                                                                     +"\n"+
							"typedef struct {"                                                     +"\n"+
							"	char *ptr;"                                                          +"\n"+
							"	int num;"                                                            +"\n"+
							"} data;"                                                              +"\n"+
							""                                                                     +"\n"+
							"data* zk_uvf_4_f1()"                                                  +"\n"+
							"{"                                                                    +"\n"+
							"	data* tmp;"                                                          +"\n"+
							""                                                                     +"\n"+
							"	tmp->ptr = NULL;"                                                    +"\n"+
							"	return tmp; "                                                        +"\n"+
							"}"                                                                    +"\n"+
							"main(){"                                                              +"\n"+
							"  data* d=zk_uvf_4_f1();"                                             +"\n"+
							"  int x=d->num; //DEFECT"                                             +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////////////39/////////////////////////////////////////////
				{
					"#include <stdio.h>"                                                   +"\n"+
							""                                                                     +"\n"+
							"void zk_uvf_5_f1(char c)"                                             +"\n"+
							"{"                                                                    +"\n"+
							"	char buf[128];"                                                      +"\n"+
							""                                                                     +"\n"+
							"	sprintf(buf, \"%c\", c); //FP"                                         +"\n"+
							"	return;"                                                             +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////////////40////////////////////////////////////////////
				{
					"#include <stdio.h>"                                                   +"\n"+
							""                                                                     +"\n"+
							"char *zk_uvf_3_f1(char *str)"                                         +"\n"+
							"{"                                                                    +"\n"+
							"	char *ptr;"                                                          +"\n"+
							""                                                                     +"\n"+
							"	for (; str != NULL; str++) {"                                        +"\n"+
							"		if (*str == 'a')"                                                   +"\n"+
							"			ptr = str; //DEFECT"                                               +"\n"+
							"	}"                                                                   +"\n"+
							"	return ptr;"                                                         +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				
				////////////////////////41/////////////////////////////////////////////
				{
					"void test2(int i) "                                                   +"\n"+
					"{"                                                                    +"\n"+
					"	int c;"                                                              +"\n"+
					"	switch(i){"                                                          +"\n"+
					"	case 1:"                                                             +"\n"+
					"		c=1;"                                                               +"\n"+
					"		break;"                                                             +"\n"+
					"	case 2:"                                                             +"\n"+
					"		c=2;"                                                               +"\n"+
					"		break;"                                                             +"\n"+
					"	case 3:"                                                             +"\n"+
					"	default:"                                                            +"\n"+
					"		c=3;"                                                               +"\n"+
					"		break;"                                                             +"\n"+
					"	}"                                                                   +"\n"+
					"    c++; //FP,UVF"                                                    +"\n"+
					"}"                                                             
					,
							"gcc"
							,
							"OK"
							,
				},				
				////////////////////////42///////////////////////////////////////////	
				{
							"void cdft(int n, int isgn, double *a, int *ip, double *w)"            +"\n"+
							"{"                                                                    +"\n"+
							"    void makewt(int nw, int *ip, double *w);"                         +"\n"+
							"    void cftfsub(int n, double *a, int *ip, int nw, double *w);"      +"\n"+
							"    void cftbsub(int n, double *a, int *ip, int nw, double *w);"      +"\n"+
							"    int nw;"                                                          +"\n"+
							""                                                                     +"\n"+
							"    nw = ip[0];"                                                      +"\n"+
							"    if (n > (nw << 2)) {"                                             +"\n"+
							"        nw = n >> 2;"                                                 +"\n"+
							"        makewt(nw, ip, w);"                                           +"\n"+
							"    }"                                                                +"\n"+
							"    if (isgn >= 0) {"                                                 +"\n"+
							"        cftfsub(n, a, ip, nw, w);"                                    +"\n"+
							"    } else {"                                                         +"\n"+
							"        cftbsub(n, a, ip, nw, w);"                                    +"\n"+
							"    }"                                                                +"\n"+
							"}"                                              
							,
							"gcc"
							,
							"OK"
							,
				},
				
/////////////////////////43////////////////////////////////////////////
				{
					"int test () {"                                                        +"\n"+
							"  int i;"                                                             +"\n"+
							"  int a =1;"                                                          +"\n"+
							"  int b = i;  //DEFECT,UVF,i"                                         +"\n"+
							"  a = i;//defect,uvf,i"                                                             +"\n"+
							"  i = 2;"                                                             +"\n"+
							"  a = i;	"                                                            +"\n"+
							"  return 0;"                                                          +"\n"+
							"}"
							,
							"gcc"
							,
							"UVF"
							,
				},			
/////////////////////////44////////////////////////////////////////////
				{
							"int test2() "                                                         +"\n"+
							"{"                                                                    +"\n"+
							"	int a;"                                                              +"\n"+
							"	a+=1;  //DEFECT,UVF,a"                                               +"\n"+
							"}"  
							,
							"gcc"
							,
							"UVF"
							,
				},			
/////////////////////////45////////////////////////////////////////////
				{
							"int test3()"                                                          +"\n"+
							"{"                                                                    +"\n"+
							"	int a;"                                                              +"\n"+
							"	a++;  //DEFECT,UVF,a"                                                +"\n"+
							"}"        
							,
							"gcc"
							,
							"UVF"
							,
				},			
/////////////////////////46////////////////////////////////////////////
				{
							"int func1(int b) "                                                    +"\n"+
							"{"                                                                    +"\n"+
							"	int a;"                                                              +"\n"+
							"	int b;"                                                              +"\n"+
							"	for (;;) {"                                                          +"\n"+
							"		a = 1;"                                                             +"\n"+
							"		break;"                                                             +"\n"+
							"	}"                                                                   +"\n"+
							"	b = a; //FP,UVF"                                                     +"\n"+
							"	return 0;"                                                           +"\n"+
							"}"      
							,
							"gcc"
							,
							"OK"
							,
				},			
/////////////////////////47////////////////////////////////////////////
				{
							"int func2_2() "                                                  +"\n"+
							"{"                                                                    +"\n"+
							"	int a;"                                                              +"\n"+
							"	int b;int i;"                                                              +"\n"+
							"	for (i= 1;;i++) {"                                              +"\n"+
							"		a = 1;"                                                             +"\n"+
							"		break;"                                                             +"\n"+
							"	}"                                                                   +"\n"+
							"	b = a; //FP,UVF"                                                     +"\n"+
							"	return 0;"                                                           +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
/////////////////////////48/////////////////////////////////////////////
				{
					"#include<stdio.h>"                                                    +"\n"+
							"void main()"                                                          +"\n"+
							"{"                                                                    +"\n"+
							"	int num,total,price;"                                                +"\n"+
							"	scanf(\"%d\", &price); //fp,UVF,price"                              +"\n"+
							"	num=10;"                                                             +"\n"+
							"	if(0==price/45)"                                                      +"\n"+
							"		{"                                                                  +"\n"+
							"			total=num+price;"                                                  +"\n"+
							"		}"                                                                  +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
/////////////////////////49/////////////////////////////////////////////
				{
					"int fun (int i)"                                                      +"\n"+
							"{"                                                                    +"\n"+
							"  return i;"                                                          +"\n"+
							"}"                                                                    +"\n"+
							"int test () {"                                                        +"\n"+
							"  int i ;"                                                            +"\n"+
							"  int j = fun ( i);  //DEFECT,UVF,i"                                  +"\n"+
							"  i = fun(2);"                                                        +"\n"+
							"  j = i;"                                                             +"\n"+
							"  return 0;"                                                          +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"UVF"
							,
				},
/////////////////////////50/////////////////////////////////////////////
				{
					"int i ;"                                                              +"\n"+
							"int main () {"                                                        +"\n"+
							"  static int j;"                                                      +"\n"+
							"  int a= i; //FP,UVF"                                                 +"\n"+
							"  a = j;   //FP,UVF"                                                  +"\n"+
							"  return 0;"                                                          +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
/////////////////////////51/////////////////////////////////////////////
				{
					"void test2(int num,int flag)     "                                    +"\n"+
					"{                                 "                                   +"\n"+
					"  int  line[1000],q;"                                                 +"\n"+
					"  flag=line[1]; "                                                     +"\n"+
					"  flag=q;//DEFECT, UVF, q"                                            +"\n"+
					"}"                                                                     
					,
					"gcc"
					,
					"UVF"
					,
		},
/////////////////////////52/////////////////////////////////////////////
		{
							"void test3(int i){"                                                   +"\n"+
							"	int value;"                                                          +"\n"+
							"	if(i==1)"                                                            +"\n"+
							"		value=1;"                                                           +"\n"+
							"	if(i==2)"                                                            +"\n"+
							"		value=2;"                                                           +"\n"+
							"	if(i==3)"                                                            +"\n"+
							"		value=3;"                                                           +"\n"+
							"	if(i<4)"                                                             +"\n"+
							"		value++;  //DEFECT, UVF, value"                                     +"\n"+
							"}"                                                                              
							,
							"gcc"
							,
							"UVF"
							,
				},
/////////////////////////53/////////////////////////////////////////////
				{
							"void test4(int i){"                                                   +"\n"+
							"	int value;"                                                          +"\n"+
							"	if(i==1)"                                                            +"\n"+
							"		value=1;"                                                           +"\n"+
							"	if(i==2)"                                                            +"\n"+
							"		value=2;"                                                           +"\n"+
							"	if(i==3)"                                                            +"\n"+
							"		value=3;"                                                           +"\n"+
							"	if(i<4&&i>0)"                                                        +"\n"+
							"		value++;  //FP,UVF"                                                 +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
/////////////////////////54/////////////////////////////////////////////
				{
					"void memset(void* a, int num, int size);"                             +"\n"+
							"int func2() {"                                                        +"\n"+
							"    int b;"                                                           +"\n"+
							"    int a[10];"                                                       +"\n"+
							"    memset(a, 0, sizeof(a));"                                         +"\n"+
							"    b = a[0]; //FP,UVF"                                               +"\n"+
							"}"     
							,
							"gcc"
							,
							"OK"
							,
				},
/////////////////////////55/////////////////////////////////////////////
				{//待写新模式(利用值的区间进行判断是否初始化)
							"#include<stdio.h>"                             +"\n"+
							"#include<memory.h>"                             +"\n"+
							"#include<string.h>"                             +"\n"+
							"typedef struct {"                                                     +"\n"+
							"	int a;"                                                            +"\n"+
							"} SA;"                                                              +"\n"+
							
							"int func1() {"                                                        +"\n"+
							"    int b;"                                                           +"\n"+
							"    SA sa;"                                                           +"\n"+
							"    memset(&sa, 0, sizeof(SA));"                                      +"\n"+
							"    b = sa.a;"                                                        +"\n"+
							"    return b; //FP,UVF"                                               +"\n"+
							"}"           
							,
							"gcc"
							,
							"OK"
							,
				},
/////////////////////////56/////////////////////////////////////////////
				{
							"void func(int *a) {"                                                  +"\n"+
							"}"                                                                    +"\n"+
							"int func4() {"                                                        +"\n"+
							"	int a;"                                                              +"\n"+
							"	func(&a);"                                                           +"\n"+
							"	int b = a; //FP,UVF"                                                 +"\n"+
							"}"            
							,
							"gcc"
							,
							"OK"
							,
				},
/////////////////////////57/////////////////////////////////////////////
				{
							"int func5()"                                                          +"\n"+
							"{"                                                                    +"\n"+
							"	int c = 1;"                                                          +"\n"+
							"	int a(c);"                                                           +"\n"+
							"	int b = a;  //FP,UVF"                                                +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
/////////////////////////58/////////////////////////////////////////////
				{
					"int func1()"                                                          +"\n"+
					"{"                                                                    +"\n"+
					"	return 1;"                                                           +"\n"+
					"}"                                                                    +"\n"+
					"int func2(int c) {"                                                   +"\n"+
					"	return 0;"                                                           +"\n"+
					"}"                                                                    +"\n"+
					"int func()"                                                           +"\n"+
					"{"                                                                    +"\n"+
					"    int	c;"                                                           +"\n"+
					"    return (c = func1()) == 1 ? 1 : func2(c); //FP,UVF"               +"\n"+
					"}"                                                                 
					,
					"gcc"
					,
					"OK"
					,
		},
/////////////////////////59/////////////////////////////////////////////
		{
				    "int read(int a, int *b ,int c);"                                      +"\n"+
					"int func3()"                                                          +"\n"+
					"{"                                                                    +"\n"+
					"    int	c;"                                                           +"\n"+
					"    return read(0, &c, (unsigned int)1) == 1 ? c : (-1); //FP,UVF"    +"\n"+
					"}"                                                                        
					,
					"gcc"
					,
					"OK"
					,
		},
/////////////////////////60/////////////////////////////////////////////
		{
			 "int read(int a, int *b ,int c);"                                      +"\n"+
					"int func4() {"                                                        +"\n"+
					"	int c;"                                                              +"\n"+
					"	read(0, (int*)&c, (unsigned int)1);"                                 +"\n"+
					"	return c; //FP,UVF"                                                  +"\n"+
					"}"                                                                     
					,
					"gcc"
					,
					"OK"
					,
		},
/////////////////////////61/////////////////////////////////////////////
		{
			 "int read(int a, int *b ,int c);"                                      +"\n"+
					"int func4() {"                                                        +"\n"+
					"	int c;"                                                              +"\n"+
					"	read(0, &c, (unsigned int)1);"                                       +"\n"+
					"	return c; //FP,UVF"                                                  +"\n"+
					"}"                                                                        
					,
					"gcc"
					,
					"OK"
					,
		},
/////////////////////////62/////////////////////////////////////////////
		{
					"int func5() {"                                                        +"\n"+
					"    int a, b;"                                                        +"\n"+
					"    a = 1;"                                                           +"\n"+
					"    (b) = (a);"                                                     +"\n"+
					"    return b - a; //FP,UVF"                                           +"\n"+
					"}"                                                                                
					,
					"gcc"
					,
					"OK"
					,
		},
/////////////////////////63/////////////////////////////////////////////
		{ 
			"int read(int a, int *b ,int c);"                                      +"\n"+
					"int func6(int a) {"                                                   +"\n"+
					"    int b;"                                                           +"\n"+
					"    if ( a > 0) {"                                                    +"\n"+
					"       b = func1();"                                                  +"\n"+
					"    } else {"                                                         +"\n"+
					"       read(0, &b, (unsigned int)1);"                                 +"\n"+
					"    }"                                                                +"\n"+
					"    return a - b; //FP,UVF"                                           +"\n"+
					"}"                                                                                   
					,
					"gcc"
					,
					"OK"
					,
		},
/////////////////////////64/////////////////////////////////////////////
		{ 
							"int func7(int a) {"                                                   +"\n"+
							"    int b;"                                                           +"\n"+
							"    int c = 0;"                                                       +"\n"+
							"    if (a > 0) {"                                                     +"\n"+
							"       b = 2;"                                                        +"\n"+
							"    }"                                                                +"\n"+
							"    if (a > 0) {"                                                     +"\n"+
							"       c = b; //FP,UVF"                                               +"\n"+
							"    }"                                                                +"\n"+
							"    return 1;"                                                        +"\n"+
							"}"                                                                                                  
							,
							"gcc"
							,
							"OK"
							,
				},
/////////////////////////65/////////////////////////////////////////////
				{ 
							"int func8(int a) {"                                                   +"\n"+
							"    int b;"                                                           +"\n"+
							"    if (a != 0) {"                                                    +"\n"+
							"       b = 2;"                                                        +"\n"+
							"    }"                                                                +"\n"+
							"    if (a == 0) {"                                                    +"\n"+
							"       return 1;"                                                     +"\n"+
							"    }"                                                                +"\n"+
							"    return b - a; //FP,UVF"                                           +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
/////////////////////////////66/////////////////////////
				{
				"int test () {"                                                        +"\n"+
				"  int i;"                                                             +"\n"+
				"  int a =2;"                                                          +"\n"+
				"  if(a != 2)"                                                         +"\n"+
				"  {"                                                                  +"\n"+
				"    a = i;"                                                           +"\n"+
				"  }"                                                                  +"\n"+
				"  a = i;   //DEFECT,UVF,i"                                            +"\n"+
				"  return 0;"                                                          +"\n"+
				"}" 
				,
				"gcc"
				,
				"UVF"
				,
				},
//////////////////////////////////////67/////////////////////////////////////	
				{
					"int func1() {"                                                        +"\n"+
					"    int a, b;"                                                        +"\n"+
					"    *(&a) = 1; //FP,UVF"                                              +"\n"+
					"    if (a == 1) {"                                                    +"\n"+
					"    	return 1;"                                                       +"\n"+
					"    }"                                                                +"\n"+
					"    return 0;"                                                        +"\n"+
					"}" 
					,
					"gcc"
					,
					"OK"
					,
				},
//////////////////////////////////////68/////////////////////////////////////	
				{
					"func4()"                                                              +"\n"+
					"{"                                                                    +"\n"+
					"	int b;"                                                              +"\n"+
					"	int a;"                                                              +"\n"+
					"	b = a;  //DEFECT,UVF,a"                                              +"\n"+
					"}"        
					,
					"gcc"
					,
					"UVF"
					,
				},
		});
	}
}