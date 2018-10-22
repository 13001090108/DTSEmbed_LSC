package softtest.test.gcc.rules.safety;


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
public class Test_BO_PRE extends ModelTestBase{
	public Test_BO_PRE(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/safety/BO_PRE-0.1.xml";
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
		                "int main(){"                                                          +"\n"+
		                "char a[10];"                                                          +"\n"+
		                "char b[100];"                                                         +"\n"+
		                "strncpy(a,b,100);"                                                     +"\n"+
		                "}"                                                                    
		                ,
		                "gcc"
		                ,
		                "BO_PRE"
		                ,
		                },

 
	///////////////// 1   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void f1(int a)"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer1[10]=\"welcome\",buffer2[10]=\"to china!\",buffer3[a];"      +"\n"+
		            "	sprintf(buffer3,\"%8s%8s\",buffer1,buffer2);"                          +"\n"+
		            "	"                                                                    +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2(int a)"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer3[a];"                                                    +"\n"+
		            "	"                                                                    +"\n"+
		            "	sprintf(buffer3,\"%8d%8d\",123,345);"                                  +"\n"+
		            "	"                                                                    +"\n"+
		            "}"                                                                    +"\n"+
		            "void f3(int a)"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer1[10]=\"welcome\",buffer2[10]=\"to china!\",buffer3[a];"      +"\n"+
		            "	"                                                                    +"\n"+
		            "	sprintf(buffer3,\"%s%8s\",buffer1,buffer2);//DEFECT"                   +"\n"+
		            "}"                                                                    +"\n"+
		            "void f4()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	int a=15;"                                                           +"\n"+
		            "	f1(a);//DEFECT"                                                      +"\n"+
		            "	f2(a);//DEFECT"                                                      +"\n"+
		            "	f3(a);"                                                              +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO_PRE"
		            ,
		            },	          
	/////////////////  2 ///////////////////	
				 {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void f1(char *p)"                                                     +"\n"+
		            "{"                                                                    +"\n"+
		            "	"                                                                    +"\n"+
		            "	scanf(\"%12s\",p);"                                            +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer[10],*p=buffer;"                                          +"\n"+
		            "	f1(p);//DEFECT"                                                      +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO_PRE"
		            ,
		            },	  
/////////////////  3   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void f1(char *p)"                                                     +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer1[10]=\"welcome\",buffer2[10]=\"to china!\";"                 +"\n"+
		            "	sprintf(p,\"%8s%8s\",buffer1,buffer2);"                                +"\n"+
		            "	"                                                                    +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2(char *p)"                                                     +"\n"+
		            "{"                                                                    +"\n"+
		            "	"                                                                    +"\n"+
		            "	sprintf(p,\"%8d%8d\",123,345);"                                        +"\n"+
		            "	"                                                                    +"\n"+
		            "}"                                                                    +"\n"+
		            "void f3(char *p)"                                                     +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer1[10]=\"welcome\",buffer2[10]=\"to china!\",buffer3[10];"      +"\n"+
		            "	"                                                                    +"\n"+
		            "	sprintf(buffer3,\"%8s%8s\",buffer1,p);"                                +"\n"+
		            "}"                                                                    +"\n"+
		            "void f4()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer1[10]=\"welcome\",buffer2[10]=\"to china!\",buffer3[10];"      +"\n"+
		            "	char *p1=buffer1,*p2=buffer2,*p3=buffer3;"                           +"\n"+
		            "	f1(p3);//DEFECT"                                                     +"\n"+
		            "	f2(p1);//DEFECT"                                                     +"\n"+
		            "	f3(p2);"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO_PRE"
		            ,
		            },	   
	/////////////////  4  ///////////////////
	 		        {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void f1(int a)"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer1[a];"                                                    +"\n"+
		            "	scanf(\"%12s\",buffer1);//DEFECT"                                      +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	int a=13;"                                                           +"\n"+
		            "	f1(a);//DEFECT"                                                      +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },	  
///////////////// 5   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void f1(int a)"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer1[10]=\"welcome\",buffer2[10]=\"to china!\",buffer3[a];"      +"\n"+
		            "	sprintf(buffer3,\"%8s%8s\",buffer1,buffer2);"                          +"\n"+
		            "	"                                                                    +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2(int a)"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer3[a];"                                                    +"\n"+
		            "	"                                                                    +"\n"+
		            "	sprintf(buffer3,\"%8d%8d\",123,345);"                                  +"\n"+
		            "	"                                                                    +"\n"+
		            "}"                                                                    +"\n"+
		            "void f3(int a)"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer1[10]=\"welcome\",buffer2[10]=\"to china!\",buffer3[a];"      +"\n"+
		            "	"                                                                    +"\n"+
		            "	sprintf(buffer3,\"%s%8s\",buffer1,buffer2);//DEFECT"                   +"\n"+
		            "}"                                                                    +"\n"+
		            "void f4()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	int a=18;"                                                           +"\n"+
		            "	f1(a);//DEFECT"                                                      +"\n"+
		            "	f2(a);//DEFECT"                                                      +"\n"+
		            "	f3(a);"                                                              +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },	            
	/////////////////  6   ///////////////////	
				  {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void f1(int a)"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer2[15]=\"1234567890\",buffer1[a];"                           +"\n"+
		            "	strcpy (buffer1,buffer2);"                                           +"\n"+
		            "	"                                                                    +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	int a=10;"                                                           +"\n"+
		            "	f1(a);//DEFECT"                                                      +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO_PRE"
		            ,
		            },	
	  
	/////////////////  7   ///////////////////	
		             {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void f1(int a)"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer2[15]=\"1234567890\",buffer1[10];"                          +"\n"+
		            "	strncat (buffer1,buffer2,a);//DEFECT"                                +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	int a=11;"                                                           +"\n"+
		            "	f1(a);"                                                              +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO_PRE"
		            ,
		            },	    
	/////////////////  8   ///////////////////	
				 {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void f1(int a)"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer2[a],buffer1[10];"                                        +"\n"+
		            "	strcpy (buffer1,\"123456789\");"                                      +"\n"+
		            "	strcpy (buffer2,buffer1);"                                           +"\n"+
		            "	"                                                                    +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2(int a)"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "	"                                                                    +"\n"+
		            "	f1(a);//DEFECT"                                                      +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f3()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	int a=9;"                                                           +"\n"+
		            "	f2(a);"                                                              +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO_PRE"
		            ,
		            },	   
	/////////////////  9   ///////////////////	
		             {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void f1(char *p)"                                                     +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer2[15]=\"1234567890\";"                                      +"\n"+
		            "	strncat (p,buffer2,10);//DEFECT"                                     +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer1[10];"                                                   +"\n"+
		            "	f1(buffer1);"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO_PRE"
		            ,
		            },	 
	/////////////////  10   ///////////////////	
				  {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void f1(char *p)"                                                     +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer2[15];"                                                    +"\n"+
		            "	strcpy (buffer2,\"1234567890\");"                                      +"\n"+
		            "	strcpy (p,buffer2);"                                                 +"\n"+
		            "	"                                                                    +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2(char *p)"                                                     +"\n"+
		            "{"                                                                    +"\n"+
		            "	"                                                                    +"\n"+
		            "	f1(p);//DEFECT"                                                      +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f3()"                                                            +"\n"+
		            "{	char buffer[10];"                                                                    +"\n"+
		            "	//char *p=buffer;"                                                    +"\n"+
		            "	f2(buffer);"                                                         +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO_PRE"
		            ,
		            },	  
	///////////////// 11   ///////////////////	
				  {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void f1(char *p)"                                                     +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer2[15]=\"1234567890\";"                                      +"\n"+
		            "	strcpy (p,buffer2);"                                                 +"\n"+
		            "	"                                                                    +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer[10];"                                                    +"\n"+
		            "	f1(buffer);//DEFECT"                                                 +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO_PRE"
		            ,
		            },	    
	/////////////////  12  ///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void f1(char *p)"                                                     +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer1[10];"                                                   +"\n"+
		            "	"                                                                    +"\n"+
		            "	strcpy (buffer1,p);"                                                 +"\n"+
		            "	"                                                                    +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer[15],*p=buffer;"                                          +"\n"+
		            "	strcpy (p,\"1234567890\");"                                            +"\n"+
		            "	f1(p);//DEFECT"                                                      +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },	 
	/////////////////  13  zys 2011.6.25	回归错误的原因：ExpressionValueVisitor中屏蔽了对于strcpy函数的处理///////////////////	
		            {
		            "#include <string.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "void f1(char *p)"                                                     +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer1[10];"                                                   +"\n"+
		            "	"                                                                    +"\n"+
		            "	strcpy (buffer1,p);"                                                 +"\n"+
		            "	"                                                                    +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	char buffer[15],*p=buffer;"                                          +"\n"+
		            "	strcpy (p,\"1234567890\");"                                            +"\n"+
		            "	f1(p);//DEFECT"                                                      +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "BO_PRE"
		            ,
		            },		                    

		 });
	 }
}
