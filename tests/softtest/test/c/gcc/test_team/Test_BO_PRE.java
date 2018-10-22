package softtest.test.c.gcc.test_team;


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
		fsmPath="softtest/rules/gcc/fault/BO_PRE-0.1.xml";
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
	

	///////////////  0   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <string.h>"                                                  +"\n"+
		            "void f1(char s[])"                                                    +"\n"+
		            "{"                                                                    +"\n"+
		            "    gets(s);//DEFECT//chh 不是BO_PRE，get函数的判断和变量无关，不需要传递函数摘要,该例为BO"                                                         +"\n"+
		            "}"                                                                    +"\n"+
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "     char s[10];"                                                     +"\n"+
		            "     f1(s);//DEFECT"                                                          +"\n"+
		            "     strcat(s, \"a\");"                                                 +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },

	/////////////////  1   ///////////////////	
//		            {
//		            "#include <string.h>"                                                  +"\n"+
//		            "void f1(char* buf)"                                                   +"\n"+
//		            "{    "                                                                +"\n"+
//		            "    char s1[] = \"Hello \";"                                            +"\n"+
//		            "    strcpy(buf, s1);"                                                 +"\n"+
//		            "}"                                                                    +"\n"+
//		            "void f2(char* buf)"                                                   +"\n"+
//		            "{    "                                                                +"\n"+
//		            "    f1(buf);"                                                         +"\n"+
//		            "    char s2[] = \"world!\";"                                            +"\n"+
//		            "    strcat(buf, s2);"                                                 +"\n"+
//		            "}"                                                                    +"\n"+
//		            "void f3()"                                                            +"\n"+
//		            "{"                                                                    +"\n"+
//		            "    char buf[10];"                                                    +"\n"+
//		            "    f2(buf);//DEFECT"                                                 +"\n"+
//		            "    char s3[] = \"OK!\";"                                               +"\n"+
//		            "    strcat(buf, s3);"                                                 +"\n"+
//		            "}"                                                                    
//		            ,
//		            "gcc"
//		            ,
//		            "BO_PRE"
//		            ,
//		            },
//
//
//	/////////////////  2   ///////////////////	
//		            {
//		            "#include <string.h>"                                                  +"\n"+
//		            "#include <stdio.h>"                                                   +"\n"+
//		            "void f1(char buf[])"                                                  +"\n"+
//		            "{"                                                                    +"\n"+
//		            "    strcat(buf, \"XX\");//DEFECT"                                       +"\n"+
//		            "}"                                                                    +"\n"+
//		            "void f2(char buf[])"                                                  +"\n"+
//		            "{"                                                                    +"\n"+
//		            "    strcat(buf, \"AAAA\");"                                             +"\n"+
//		            "}"                                                                    +"\n"+
//		            "void f3()"                                                            +"\n"+
//		            "{"                                                                    +"\n"+
//		            "    char buf[10];"                                                    +"\n"+
//		            "    gets(buf);"                                                       +"\n"+
//		            "    if(strlen(buf) < 3)"                                              +"\n"+
//		            "        f2(buf);"                                                     +"\n"+
//		            "    else"                                                             +"\n"+
//		            "        f1(buf);//DEFECT"                                             +"\n"+
//		            "}"                                                                    
//		            ,
//		            "gcc"
//		            ,
//		            "BO_PRE"
//		            ,
//		            },
/*
 * 关于以上1,2用例，事实上，目前系统的区间运算根本没达到上面用例要求的精确度
 * 用例1：在f2调用f1后，系统并不知道f1对buf造成了什么影响，buf的dimain并未改变,所以在f3调用f2时以f3定义的buf可用空
 * 间为10来判断f2的strcat，并没有 溢出
 * 用例2:在f3中，if判断后产生的可能may、must域和buf的domain并无关联起来，而gets本身到底向buf写入多少内容编译时未知
 * ，所以在判断f2和f1是否引起溢出时buf的空间仍以10计算
*/
	
//		        	/////////////////  3   ///////////////////	
//		            {
//		            "#include <string.h>"                                                  +"\n"+
//		            "char s[8];"                                                           +"\n"+
//		            "void f1()"                                                            +"\n"+
//		            "{"                                                                    +"\n"+
//		            "    strcat(s, \"12\");     "                                            +"\n"+
//		            "}"                                                                    +"\n"+
//		            "void f2()"                                                            +"\n"+
//		            "{"                                                                    +"\n"+
//		            "    f1();"                                                            +"\n"+
//		            "    strcat(s, \"54321\");//DEFECT     "                                         +"\n"+
//		            "}"                                                                    +"\n"+
//		            "void f3()"                                                            +"\n"+
//		            "{"                                                                    +"\n"+
//		            "     strcat(s, \"98\"); "                                               +"\n"+
//		            "     f2();//DEFECT          "                                                 +"\n"+
//		            "}"                                                                    
//		            ,
//		            "gcc"
//		            ,
//		            "BO_PRE"
//		            ,
//		            },
	/////////////////  4   ///////////////////	
//		            {
//		            "#include <string.h>"                                                  +"\n"+
//		            "char s[8];"                                                           +"\n"+
//		            "void f1()"                                                            +"\n"+
//		            "{"                                                                    +"\n"+
//		            "    strcat(s, \"12345\");//DEFECT     "                                         +"\n"+
//		            "}"                                                                    +"\n"+
//		            "void f2()"                                                            +"\n"+
//		            "{"                                                                    +"\n"+
//		            "    f1();//DEFECT"                                                            +"\n"+
//		            "    strcat(s, \"54321\");     "                                         +"\n"+
//		            "}"                                                                    +"\n"+
//		            "void f3()"                                                            +"\n"+
//		            "{"                                                                    +"\n"+
//		            "     strcat(s, \"9876\"); "                                             +"\n"+
//		            "     f2(); //DEFECT         "                                                 +"\n"+
//		            "}"                                                                    
//		            ,
//		            "gcc"
//		            ,
//		            "BO_PRE"
//		            ,
//		            },
/*
 * chh 3,4同用例1一样，用例3,4也是由于strcat函数的作用结果没有在变量的domain上体现出来，导致接下来的判断误差
 * 为例测试全局变量的函数摘要传递将以上两个用例修改如下		            
 */
		            {
			            "#include <string.h>"                                                  +"\n"+
			            "char s[8];"                                                           +"\n"+
			            "void f1()"                                                            +"\n"+
			            "{"                                                                    +"\n"+
			            "    strcpy(s, \"12345678\");     "                                            +"\n"+
			            "}"                                                                    +"\n"+
			            "void f2()"                                                            +"\n"+
			            "{"                                                                    +"\n"+
			            "    f1();"                                                            +"\n"+
			            " "                                         +"\n"+
			            "}"                                                                    +"\n"+
			            "void f3()"                                                            +"\n"+
			            "{"                                                                    +"\n"+
			            " "                                               +"\n"+
			            "     f2();//DEFECT  "                                                 +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "BO_PRE"
			            ,
			            },				 				 
	/////////////////  5   ///////////////////	
//		            {
//		            "#include <string.h>"                                                  +"\n"+
//		            "char a[20];"                                                          +"\n"+
//		            "char b[5];"                                                           +"\n"+
//		            ""                                                                     +"\n"+
//		            "void f1()"                                                            +"\n"+
//		            "{"                                                                    +"\n"+
//		            "    strcat(a, b);"                                                    +"\n"+
//		            "}"                                                                    +"\n"+
//		            "void f()"                                                             +"\n"+
//		            "{"                                                                    +"\n"+
//		            "    int i;"                                                           +"\n"+
//		            "    for(i=0; i<5; i++)"                                               +"\n"+
//		            "        f1(); //DEFECT   "                                                    +"\n"+
//		            "}"                                                                    
//		            ,
//		            "gcc"
//		            ,
//		            "BO_PRE"
//		            ,
//		            },

/*
 * 用例5无法判断，理由同用例1，在第二次循环的时候，第一次f1的分析并没有对a的domain造成改变
 */
 		            
	

		 });
	 }
}
