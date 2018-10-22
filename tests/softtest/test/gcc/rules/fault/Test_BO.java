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
public class Test_BO extends ModelTestBase{
	public Test_BO(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/BO-0.1.xml";
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
	/////////////////  0   ///////////////////	
		            {
			            "#include <stdio.h> "                                                                    +"\n"+

		            "void fopen_compchk()"                                                +"\n"+
		            "{ "                                                                   +"\n"+
		            " char tmpfile[16384];"                                                +"\n"+
		            " fopen_comp(tmpfile, 1);"                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void fopen_comp(const char *file, int flag)"                         +"\n"+
		            "{"                                                                    +"\n"+
		            "   "                                                                  +"\n"+
		            "   char command[16384];"                                              +"\n"+
		            "   if (flag) "                                                        +"\n"+
		            "   {"                                                                 +"\n"+
		            "       sprintf(command, \"gzip.exe -d -c %s\", file);"                                +"\n"+
		            "   }"                                                                 +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
//////////////////////////  1  /////////////////////////////////////
		            {
			       "#include <string.h> "                                                                    +"\n"+

		            "void fopen_compchk(char *file)"                                                +"\n"+
		            "{ "                                                                   +"\n"+
		            " char tmpfile[16384];"                                                +"\n"+
		            "  strcpy(tmpfile, file);"                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
	///////////////// 1   ///////////////////	
		           {
		            ""                                                                     +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void f1()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer1[10];"                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "	gets(buffer1);//DEFECT"                                              +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },	         
		            
	/////////////////  2  ///////////////////	
		            {
		            ""                                                                     +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void f1()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer2[10],buffer1[10];"                                       +"\n"+
		            "	scanf(\"%12s\",buffer1);//DEFECT"                                      +"\n"+
		            "	scanf(\"%8s%s\",buffer1,buffer2);//DEFECF"                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },	             
	/////////////////  3   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void f1()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer1[10]=\"welcome\",buffer2[10]=\"tochina\",buffer3[15];"       +"\n"+
		         //   "	sprintf(buffer3,\"%6s%s\",buffer1,buffer2);"                           +"\n"+
		        //    "	sprintf(buffer3,\"%7d%8d\",123,345);//DECFECT"                         +"\n"+
		            "	sprintf(buffer3,\"%s%8s\",buffer1,buffer2);//DECFECT"                  +"\n"+
		            "}"                                                                    +"\n"+
//		            ""                                                                     +"\n"+
//		            ""                                                                     +"\n"+
//		            "void f2(char *q){"                                                    +"\n"+
//		            "     char buffer[10],buffer1[11]=\"1234567890\";"                       +"\n"+
//		            "     char *p=buffer1;"                                                +"\n"+
//		            "     sprintf(buffer,\"%s\",\"1234567890\");//DECFECT"                              +"\n"+
//		            "     sprintf(buffer,\"%s\",p);//DECFECT"                                         +"\n"+
//		            "     sprintf(buffer,\"%s\",buffer1);//DECFECT"                                   +"\n"+
//		            "     sprintf(buffer,\"%s\",q);//DECFECT"                                         +"\n"+
		            "     }"                                                               
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },	 
	/////////////////  3   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void f1()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffe1[10],*p=buffer;"                                          +"\n"+
		            ""                                                                     +"\n"+
		            "	gets(p);//DEFECT"                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },  
	/////////////////  4   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void f1()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer2[10],buffer1[10],*p1=buffer1,*p2=buffer2;"               +"\n"+
		            "	scanf(\"%12s\",p1);//DEFECT"                                           +"\n"+
		            "	scanf(\"%8s%s\",buffer1,p2);//DEFECF"                                  +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },	
	/////////////////  5   ///////////////////	
		            {
		            ""                                                                     +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void f1()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer2[10],buffer1[10];"                                       +"\n"+
		            "	scanf(\"%9s\",buffer1);"                                      +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  6   ///////////////////	
		            {
		            ""                                                                     +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void f1()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer1[10]=\"welcome\",buffer2[10]=\"tochina\",buffer3[15];"       +"\n"+
		            "	sprintf(buffer3,\"%6s%s\",buffer1,buffer2);"                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },	           
	/////////////////  7   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void f1()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer2[15]=\"1234567890\",buffer1[10];"                          +"\n"+
		            "	strcpy (buffer1,buffer2);//DEFECT"                                   +"\n"+
		            "	"                                                                    +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
	/////////////////  8   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void f1()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer1[10];"                                                   +"\n"+
		            "	strcpy (buffer1,\"1234567890\");//DEFECT"                              +"\n"+
		            "	"                                                                    +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
	/////////////////  9   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void f1()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	int a=11;"                                                           +"\n"+
		            "	char buffer2[15]=\"1234567890\",buffer1[10];"                          +"\n"+
		            "	strncat (buffer1,buffer2,11);//DEFECT"                               +"\n"+
		            "	strncat (buffer1,buffer2,a);//DEFECT"                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },	          
	/////////////////  10   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void f1()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer1[10],*p=buffer1;"                                        +"\n"+
		            "	strcpy (p,\"1234567890\");//DEFECT"                                    +"\n"+
		            "	"                                                                    +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },	      
	/////////////////  11   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void f1()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer2[15]=\"1234567890\",buffer1[10],*p1=buffer1,*p2=buffer2;"  +"\n"+
		            "	strcpy (buffer1,p2);//DEFECT"                                        +"\n"+
		            "	strcpy (p1,buffer2);//DEFECT"                                        +"\n"+
		            "	"                                                                    +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
	///////////////// 12   ///////////////////	
		            {
		            ""                                                                     +"\n"+
		            ""                                                                     +"\n"+
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void f1()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	int a=6;"                                                            +"\n"+
		            "	char buffer2[10]=\"WELCOME\",buffer1[5],*p1=buffer1,*p2=buffer2;"      +"\n"+
		            "	strncat(p1,buffer2,6);//DEFECT"                                      +"\n"+
		            "	strncat(p1,buffer2,5);//DEFECT"                                      +"\n"+
		            "	strncat(buffer1,p2,a);//DEFECT"                                      +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },	 
	/////////////////  13  ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void f1()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer1[10],*p=buffer1;"                                        +"\n"+
		            "	strcpy (p,\"123456789\");//DEFECT"                                    +"\n"+
		            "	"                                                                    +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },	  
	/////////////////  14  ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void f1()"                                                            +"\n"+
		            "{	char buffer1[10]=\"123\";"                                                                    +"\n"+
		            "	char *p=buffer1;"                                        +"\n"+
		            "	strcat (p,\"456789\");//DEFECT"                                    +"\n"+
		            "	"                                                                    +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },	 	            
	/////////////////  15   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "int f1(){"                                                            +"\n"+
		            "    int a=3,b;"                                                       +"\n"+
		            "    if(a==3) b=10;"                                                   +"\n"+
		            "    else b=9;"                                                        +"\n"+
		            "    return b;"                                                        +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2(){"                                                           +"\n"+
		            "     int a;"                                                          +"\n"+
		            "     a=f1();"                                                         +"\n"+
		            "     char buffer[a];"                                                 +"\n"+
		            "     strcpy(buffer,\"1234567890\");"                                    +"\n"+
		            "     //strncat(buffer,\"1234567890\",a);"                               +"\n"+
		            "     }"                                                               
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },	
	/////////////////  16   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "int f1(){"                                                            +"\n"+
		            "    int a=3,b;"                                                       +"\n"+
		            "    if(a==3) b=9;"                                                   +"\n"+
		            "    else b=10;"                                                        +"\n"+
		            "    return b;"                                                        +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2(){"                                                           +"\n"+
		            "     int a;"                                                          +"\n"+
		            "     a=f1();"                                                         +"\n"+
		            "     char buffer[9];"                                                 +"\n"+
		            "     //strcpy(buffer,\"1234567890\");"                                    +"\n"+
		            "     strncat(buffer,\"1234567890\",a);"                               +"\n"+
		            "     }"                                                               
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },	   
	/////////////////  17   ///////////////////	
		            {
			            "#include <string.h>"                                                  +"\n"+
			            ""                                                                     +"\n"+
			            "int f1(){"                                                            +"\n"+
			            "    int a=3,b;"                                                       +"\n"+
			            "    if(a==3) b=9;"                                                   +"\n"+
			            "    else b=10;"                                                        +"\n"+
			            "    return b;"                                                        +"\n"+
			            "}"                                                                    +"\n"+
			            "void f2(){"                                                           +"\n"+
			            "     int a;"                                                          +"\n"+
			            "     a=f1();"                                                         +"\n"+
			            "     char buffer[10];"                                                 +"\n"+
			            "     //strcpy(buffer,\"1234567890\");"                                    +"\n"+
			            "     strncat(buffer,\"1234567890\",a);"                               +"\n"+
			            "     }"                                                               
			            ,
			            "gcc"
			            ,
			            "OK"
			            ,
			            },	             
	 
	/////////////////  18   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "int all=7;"                                                           +"\n"+
		            "void f3(){"                                                           +"\n"+
		            "     all=8;"                                                          +"\n"+
		            "     }"                                                               +"\n"+
		            "void f4(){"                                                           +"\n"+
		            "     char buffer[8];"                                                 +"\n"+
		            "     f3();"                                                         +"\n"+
		            "     strncat(buffer,\"123456789\",all);"                                +"\n"+
		            "     }"                                                               
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },
	/////////////////  19   ///////////////////	  
		            {
			            "#include <string.h>"                                                  +"\n"+
			            ""                                                                     +"\n"+
			            "int a=8;"                                                           +"\n"+
			            "void f3(){"                                                           +"\n"+
			            "     a=7;"                                                          +"\n"+
			            "     }"                                                               +"\n"+
			            "void f4(){"                                                           +"\n"+
			            "     char buffer[8];"                                                 +"\n"+
			            "     f3();"                                                           +"\n"+
			            "     strncat(buffer,\"123456789\",a);"                                +"\n"+
			            "     }"                                                               
			            ,
			            "gcc"
			            ,
			            "OK"
			            ,
			            },	            
	/////////////////  20   ///////////////////	
			        {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "     int i=0;"                                                        +"\n"+
		            "     for(;i<10;i++){"                                                 +"\n"+
		            "     if(i==5)"                                                        +"\n"+
		            "             break;"                                                  +"\n"+
		            "     }"                                                               +"\n"+
		            "     char buffer[i];"                                                 +"\n"+
		            "     strcpy(buffer,\"123456\");"                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },	
	/////////////////  21   ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "     int i=10,j=0;"                                                   +"\n"+
		            "     if(i<8)"                                                         +"\n"+
		            "            j++;"                                                     +"\n"+
		            "     if(i>=8)"                                                        +"\n"+
		            "             i=(j==1?10:9);"                                          +"\n"+
		            "     char  buffer[i];"                                                +"\n"+
		            "     strcpy(buffer,\"123456789\");"                                     +"\n"+
		            "     }"                                                               
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },	
	/////////////////  22  ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "     int i=0;"                                                        +"\n"+
		            "     while(i<10){"                                                    +"\n"+
		            "     if(i==5)"                                                        +"\n"+
		            "             break;"                                                  +"\n"+
		            "	i++;"                                                                +"\n"+
		            "     }"                                                               +"\n"+
		            "     char buffer[i];"                                                 +"\n"+
		            "     strcpy(buffer,\"123456\");"                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },	 
   ///////////////// 23  ///////////////////	
		            {
		            "#include  <stdio.h>"                                                  +"\n"+
		            "int all=8;"                                                           +"\n"+
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "     all=6;"                                                          +"\n"+
		            "}"                                                                    +"\n"+
		            "void f1(){"                                                           +"\n"+
		            "     f();"                                                            +"\n"+
		            "     char buffer[all];"                                               +"\n"+
		            "     scanf(\"%7s\",buffer);"                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },	           
/////chh   BO的用例暂时添加这么多	   //修改后的区间运算方式下全局变量在本地未赋值的情况下其值为unknown，则本用例失效
					///////////////// 24  ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            "int a;void f(){a=11;}"                                                            +"\n"+
		            "void f1(){"                                                           +"\n"+
		            "f();char buffer[10];"                                                      +"\n"+
		            "strncat(buffer,\"1234567890\",a);"                                      +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO"
		            ,
		            },		
			 
		 });
	 }
}

