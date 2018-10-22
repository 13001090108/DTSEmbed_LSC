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
public class Test_UVF_P extends ModelTestBase{
	public Test_UVF_P(String source,String compiletype, String result)
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
////////////////////////////////  0   ////////////////////////////////////////	
		            {
		            "int test_uvf_p_1(){"                                                  +"\n"+
		            "    int *p;"                                                          +"\n"+
		            "    int a=*p;//defect"                                                +"\n"+
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
		            "#include <stdlib.h>"                                                  +"\n"+
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
		                "#include <stdlib.h>"                                                  +"\n"+
		                "int test_uvf_p_2(){"                                                  +"\n"+
		                "    int *p;"                                                          +"\n"+
		                "    *p=1;"                                                            +"\n"+
		                "    p=malloc(sizeof(int *)*3);"                                       +"\n"+
		                "    int a[3];"                                                        +"\n"+
		                "    a[1]=p[0];//defect"                                               +"\n"+
		                "    return 0;"                                                        +"\n"+
		                "    }"                                                                
		                ,
		                "gcc"
		                ,
		                "OK"
		                ,
		                },
///////////////////////////////  3   ///////////////////	
		                {
			            "#include <stdlib.h>"                                                  +"\n"+
		                "int test_uvf_p_3(){"                                                  +"\n"+
		                "    char *p;"                                                         +"\n"+
		                "    char *s;"                                                         +"\n"+
		                "    p=malloc(sizeof(char *)*6);"                                      +"\n"+
		                "    strcpy(s,p);//defect,uvf_p,p"                                             +"\n"+
		                "    return 0;"                                                        +"\n"+
		                "    }"                                                                
		                ,
		                "gcc"
		                ,
		                "UVF_P"
		                ,
		                },
//////////////////////////////////4////////////////////
		                {
		                "#include<stdio.h>"                                                    +"\n"+
		                "int test_uvf_p_4(){"                                                  +"\n"+
		                "    char *p;"                                                         +"\n"+
		                "    printf(\"%c\",p);//defect,uvf_p,p"                                          +"\n"+
		                "    return 0;"                                                        +"\n"+
		                "    }"                                                                
		                ,
		                "gcc"
		                ,
		                "OK"
		                ,
		                },
/////////////////////////////////  5   ///////////////////	
		                {//scanf,sscanf待解决
		                "#include<stdio.h>"                                                    +"\n"+
		                "int test_uvf_p_5(){"                                                  +"\n"+
		                "    char *p;"                                                         +"\n"+
		                "	scanf(\"%c\",p);"                                                      +"\n"+
		                "    printf(\"%c\",p);"                                                  +"\n"+
		                "    return 0;"                                                        +"\n"+
		                "    }"                                                                
		                ,
		                "gcc"
		                ,
		                "OK"
		                ,
		                }, 
/////////////////  6   ///////////////////	
		                {
		                "#include<stdio.h>"                                                    +"\n"+
		                "int test_uvf_p_5(){"                                                  +"\n"+
		                "    char *p;"                                                         +"\n"+
		                "    if(1){"                                                           +"\n"+
		                "          p[0]=1; //defect"                                                    +"\n"+
		                "    }"                                                                +"\n"+
		                "   // printf(\"%c\",p);"                         +"\n"+
		                "    return 0;"                                                        +"\n"+
		                "    }"                                                                
		                ,
		                "gcc"
		                ,
		                "OK"
		                ,
		                },
//////////////////////////////7///////////////////////////////////		                
			            {//scanf,sscanf待解决
				            "void fun()"                                                           +"\n"+
				            "{"                                                                    +"\n"+
				            "	char c[],d[];"                                                         +"\n"+
				                                                               
				            "	sscanf(\"123456\",\"%s\",c);//FP"                                            +"\n"+
				            "	d=c;;"                                                        +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            
				            "OK"
				            ,
				            },
/////////////////  8 strcpy初始化 ///////////////////	
				             {
				            "void fun()"                                                           +"\n"+
				            "{"                                                                    +"\n"+
				            "char st1[],st2[]=\"aaaaa\";"                                                  +"\n"+
				            "strcpy(st1,st2);"                                                    +"\n"+
				            "}" 
				            ,
				            "gcc"
				            ,
				            
				            "OK"
				            ,
				            },
/////////////////  9 strcpy初始化不合法 ///////////////////	
				             {
				            "void fun()"                                                           +"\n"+
				            "{"                                                                    +"\n"+
				            "char st1[];"                                                  +"\n"+
				            "strcpy(st1,st1);"                                                    +"\n"+
				            "}" 
				            ,
				            "gcc"
				            ,
				            
				            "OK"
				            ,
				            },
///////////////// 10 strcpy初始化不合法 ///////////////////	
						  {
				            "void fun()"                                                           +"\n"+
				            "{"                                                                    +"\n"+
				            "char str2[],str1[];"                                                  +"\n"+
				            "strcpy(str1,str2);"                                                    +"\n"+
				            "}" 
				            ,
				            "gcc"
				            ,
				            
				            "OK"
				            ,
				            },
/////////////////  11  chh  指针初始化///////////////////	
				    		
				            {
				            "fun()"                                                                +"\n"+
				            "{"                                                                    +"\n"+
				            "int a[],*p;"                                                        +"\n"+
				            "p=a;//defect,UVF_P,a"                                                                +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "OK"
				            ,
				            },
/////////////////  12  chh  指针初始化///////////////////	
				    		
				            {
				            "fun()"                                                                +"\n"+
				            "{"                                                                    +"\n"+
				            "	int a[],b[];"                                                        +"\n"+
				            "	int b=a;//defect,UVF_P,a"                                                                +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "OK"
				            ,
				            },
/////////////////  13   chh 数组初始化不合法///////////////////	
				    		
				            {
				            "fun()"                                                                +"\n"+
				            "{"                                                                    +"\n"+
				            "	int a[];"                                                        +"\n"+
				            "	a[0]=a[1];//DEFECT,UVF_P,a"                                                                +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "OK"
				            ,
				            },		
/////////////////  14   chh  数组初始化///////////////////	
				    		
				            {
				            "fun()"                                                                +"\n"+
				            "{"                                                                    +"\n"+
				            "	int a[];"                                                        +"\n"+
				            "	a[0]=a[1]=0;"                                                                +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "OK"
				            ,
				            },	
/////////////////  15  chh strcpy初始化 //////////////////
				            {
				            "void fun()"                                                           +"\n"+
				            "{"                                                                    +"\n"+
				            "char st1[],st2[];"                                                  +"\n"+
				            "strcmp(st1,st2);//defect,uvf_p,st1,st2"                                                    +"\n"+
				            "}" 
				            ,
				            "gcc"
				            ,
				            
				            "OK"
				            ,
				            },	
////////////////  16 chh switch初始化不可达   ///////////////////	
				            {
				            "void fun()"                                                           +"\n"+
				            "{"                                                                    +"\n"+
				            "int i;"                                                    +"\n"+
				            "int *a;"                                                       +"\n"+
				            "int *b;"                                                         +"\n"+
				            "i=0;"                                                                   +"\n"+
				            "switch(i)"                                                            +"\n"+
				            "{"                                                                    +"\n"+
				            "case 1:a[0]=2;break; //"                                                    +"\n"+
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
				            "char* a;"                                                              +"\n"+
				            "do{a++;a[0]=0;}while(1);//defect"                                                      +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "OK"
				            ,
				            },	
			/////////////////  18 ///////////////////	
				            {
				            "#include <string.h>"                                                  +"\n"+
				            "#include <stdlib.h>"                                                  +"\n"+
				            "void f(){"                                                            +"\n"+
				            "   int* p,*q;"                                                        +"\n"+
				            "   p=(int*)malloc(11);"                                               +"\n"+
				            "   strcpy(p,\"1243\");"                                                 +"\n"+
				            "   *p; "                                                              +"\n"+
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
