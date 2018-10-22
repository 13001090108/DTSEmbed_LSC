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
public class MLF_EXP extends ModelTestBase {
	public MLF_EXP(String source,String compiletype, String result)
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
		LIB_SUMMARYS_PATH="gcc_lib/mm_summary.xml";
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
	/////////////////  1   ///////////////////	
		            {
		            "#include \"stdlib.h\""                                                  +"\n"+
		            "void ghx_mlf_4_f4(int i)"                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "	int a[5]={4,4,4,4,4};"                                              +"\n"+
		            "	int* m4=NULL;"                                                       +"\n"+
		            "	if(i>0){"                                                            +"\n"+
		            "		m4=a;"                                                              +"\n"+
		            "	}else{"                                                              +"\n"+
		            "		m4=(int*)malloc(100);"                                              +"\n"+
		            "	}"                                                                   +"\n"+
		            "	if(i>0)"                                                     +"\n"+
		            "	{"                                                                   +"\n"+
		            "		free(m4);"                                                          +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    +"\n"+
		            "void ghx_mlf_4_f5(int i)"                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "MLF"
		            ,
		            },
	/////////////////  2   ///////////////////	
		            {
		            "#include <malloc.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "void ghx_mlf_5_f5()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "char *p = (char*)malloc(100);"                                        +"\n"+
		            ""                                                                     +"\n"+
		            "delete(p); //DEFECT"                                                  +"\n"+
		            "  "                                                                   +"\n"+
		            "}"                                                                    +"\n"+
		            "void ghx_mlf_5_f1(int i)"                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "char *p=(char*)malloc(100);"                                          +"\n"+
		            "free(p);"                                                             +"\n"+
		            "if(i>0)"                                                              +"\n"+
		            "free(p);//DEFECT"                                                     +"\n"+
		            "}"                                                                    +"\n"+
		            "void ghx_mlf_5_f2()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "char *p = (char*)malloc(100);"                                        +"\n"+
		            ""                                                                     +"\n"+
		            "free(p); //FP"                                                        +"\n"+
		            "  "                                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "MLF"
		            ,
		            },
	/////////////////  3   ///////////////////	
		            {
		            "#include \"stdio.h\""                                                   +"\n"+
		            "#include \"stdlib.h\""                                                  +"\n"+
		            "void ghx_mlf_6_f6()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "int i;"                                                               +"\n"+
		            "char* p2 = (char*)malloc( 5*sizeof(char));"                           +"\n"+
		            ""                                                                     +"\n"+
		            "for( i=0; i< 5; i++ )"                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "printf(\"abc\");"                                                       +"\n"+
		            "}"                                                                    +"\n"+
		            "free (p2);//DEFECT"                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  4   ///////////////////	
		            {
		            	"#include<stdlib.h>"                                                  +"\n"+
		            "void fun1(int flag,int *p){"                                          +"\n"+
		            "	if(flag)"                                                            +"\n"+
		            "		free(p);"                                                           +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    +"\n"+
		            "void fun2(int *p){"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "		free(p);"                                                           +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    +"\n"+
		            "void f(int flag){"                                                    +"\n"+
		            "	int *p=malloc(sizeof(int));"                                         +"\n"+
		            "	int *q=malloc(sizeof(int));"                                         +"\n"+
		            "	fun1(flag,p);  //DEFECT"                                             +"\n"+
		            "	fun2(q);   //FP"                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "MLF"
		            ,
		            },
	/////////////////  5   ///////////////////	
		            {
		            "#include <malloc.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "void jhb_mlf_4_f1(unsigned int i)"                                    +"\n"+
		            "{"                                                                    +"\n"+
		            "char *p = (char*)malloc(12);"                                         +"\n"+
		            "if(i>0) {"                                                            +"\n"+
		            "free(p); "                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            "return;   //DEFECT"                                                       +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "MLF"
		            ,
		            },
	/////////////////  6   ///////////////////	
		            {
		            "#include <malloc.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            "void f(unsigned int i){"                                              +"\n"+
		            "	int *memleak_error=malloc(sizeof(int));"                             +"\n"+
		            "    if (i>0) return;"                                                 +"\n"+
		            "	free (memleak_error);   //DEFECT"                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "MLF"
		            ,
		            },
	/////////////////  7   ///////////////////	
		            {
		            "void fun2(int *p){"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "		free(p);"                                                           +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    +"\n"+
		            "void fun3(int *p){"                                                   +"\n"+
		            "	fun2(p);"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f(int flag){"                                                    +"\n"+
		            "	int *p=malloc(sizeof(int));"                                         +"\n"+
		            "	"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "	fun3(p);   //FP"                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  8   ///////////////////	
		            {
		            "int flag;"                                                            +"\n"+
		            "void fun2(int *p){"                                                   +"\n"+
		            "        if(p)"                                                        +"\n"+
		            "		   free(p);"                                                        +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f(){"                                                            +"\n"+
		            "	int *p=malloc(sizeof(int));"                                         +"\n"+
		            "	fun2(p);"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  9   ///////////////////	
		            {
		            	"#include<stdlib.h>"                                                  +"\n"+
		            "   void foo()"                                                        +"\n"+
		            "   {"                                                                 +"\n"+
		            "     int *ptr = malloc(sizeof(int));"                                 +"\n"+
		            "     *ptr = 25;"                                                      +"\n"+
		            "     ptr = malloc(sizeof(int)); //DEFECT"                             +"\n"+
		            "     *ptr = 35;"                                                      +"\n"+
		            "  } //"                                                               
		            ,
		            "gcc"
		            ,
		            "MLF"
		            ,
		            },
	/////////////////  10   ///////////////////	
		            {
		            "#include<stdlib.h>"                                                  +"\n"+	
		            "#include <assert.h>"                                                  +"\n"+
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_mlf_2_f1(int flag,char *p)"                                   +"\n"+
		            "{   "                                                                 +"\n"+
		            "     if(flag)"                                                        +"\n"+
		            "         free(p);"                                                    +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_mlf_2_f2(int flag)"                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *buf = malloc(10*sizeof(char));"                                +"\n"+
		            ""                                                                     +"\n"+
		            "	zk_mlf_2_f1(flag,buf); //DEFECT"                                     +"\n"+
		            ""                                                                     +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "MLF"
		            ,
		            },
	/////////////////  11   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "int* func()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	int *ptr = (int*)malloc(sizeof(int));"                               +"\n"+
		            ""                                                                     +"\n"+
		            "	return ptr ? ptr : (int*)malloc(sizeof(int));"                       +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            //"MLF"
		            "OK"
		            ,
		            },
	/////////////////  12  ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "typedef struct{"                                                   +"\n"+
		            "   char a[12];"                                                       +"\n"+
		            "   char b[34];"                                                       +"\n"+
		            "   int i;"                                                            +"\n"+
		            "   int *p;"                                                           +"\n"+
		            "}S;"                                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void f(){"                                                            +"\n"+
		            "   "                                                                  +"\n"+
		            "   S  *s;"                                                            +"\n"+
		            "   s->p=(int*)malloc(10);"                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "MLF"
		            ,
		            },
	/////////////////  13   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            ""                                                                     +"\n"+
		            "typedef struct{"                                                   +"\n"+
		            "   char a[12];"                                                       +"\n"+
		            "   char b[34];"                                                       +"\n"+
		            "   int i;"                                                            +"\n"+
		            "   char *p;"                                                          +"\n"+
		            "}S;"                                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "char* f(){"                                                           +"\n"+
		            "   "                                                                  +"\n"+
		            "   return (char*)malloc(10);"                                         +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f1(){"                                                           +"\n"+
		            "   S  *s;"                                                            +"\n"+
		            "   s->p=f(); "                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "MLF"
		            ,
		            },
	/////////////////  14  ///////////////////	
		            //xwt:过程内MLF不识别全局变量，此类判断原属MLFPost，改动中遇到以下问题
		            //xwt:函数特征局限性（只保存了variable，缺少创建状态机信息VariableNameDeclaration）需要改动的地方多，待完善
		            /*暂时想不出两全其美的方法：
		             * 首先有这样一个区别，VariableNameDeclaration存了变量在语法树上的位置信息，即节点信息
		             * 1，状态机正常运转必须要VariableNameDeclaration，因为要用到变量的语法树节点信息来生成描述信息，而且所
		             *    有的查找比对存储机制均围绕VariableNameDeclaration展开，要改动是不理智的
		             * 2，一般情况，分配特征MethodMMFeature确实只要variable信息即可，没必要去存VariableNameDeclaration和节
		             *    点信息，因为是跨函数的分配，可以说根本就不用不在乎这些位置信息，只要知道是某某函数里分配的就是了，如果
		             *    是通过参数或返回值来分配，我们记录分配变量的位置信息没有意义所以若对于非全局变量分配的大部分情况，
		             *    存了也是冗余。
		             * 3，尝试过在f1中的f()节点再搜索语法树人为找到variable的节点信息，但状态机是在单个函数内运作的。这么做已经
		             *    跨出本函数了，在模块之间又加了莫名其妙的耦合性。而且操作麻烦，造成的后果也未知
		             * 我稍后继续考虑，*/
		            //xwt:鉴于现在这种疑惑，我觉得是不是还是得用MLFPost模式还解决问题，之前取消post是为什么？
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
	/////////////////  15   ///////////////////	
	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "int flag;"                                                            +"\n"+
		            "void fun2(int *p){"                                                   +"\n"+
		            "        if(p)"                                                        +"\n"+
		            "		   free(p);"                                                        +"\n"+
		            ""                                                                     +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void f(){"                                                            +"\n"+
		            "	int *p=(int*)malloc(1);"                                             +"\n"+
		            "	fun2(p);"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
//////////////////////////16//////////////////////////////////////////////
					//jdh：存在漏报问题，考虑循环结构后应该可以解决
					//st: 重复分配空间问题，目前未考虑
		            {
		            "#include \"stdlib.h\""                                                  +"\n"+
		            "void *ghx_mlf_1_f1()"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	int cc;"                                                             +"\n"+
		            "	char *ff;"                                                           +"\n"+
		            ""                                                                     +"\n"+
		            "	for (cc=0; cc<500; cc++)"                                            +"\n"+
		            "	{"                                                                   +"\n"+
		            "		ff=(char*)malloc(10);"                                              +"\n"+
		            "	}"                                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "	free (ff);//DEFECT"                                                  +"\n"+
		            "	return 0;"                                                           +"\n"+
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
