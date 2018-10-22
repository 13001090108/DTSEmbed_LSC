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
public class UVF_Exp extends ModelTestBase {
	public UVF_Exp(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/UVF_Exp-0.1.xml";
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
				//总用例：7
				//未通过用例：2
				//未通过用例序号:1,5
				///////////////////////////////////0//////////////////////////////////////////////
				{
					"#include <stdlib.h>  "                                                +"\n"+
							"struct s {"                                                           +"\n"+
							"    int i;"                                                           +"\n"+
							"  };"                                                                 +"\n"+
							"  "                                                                   +"\n"+
							"  int f(struct s *v, int t) {"                                        +"\n"+
							"    v = (struct s *)malloc(sizeof(struct s));"                        +"\n"+
							"    if (t > 0) {"                                                     +"\n"+
							"      v->i = t;"                                                      +"\n"+
							"    }"                                                                +"\n"+
							"   return v->i;"                                             +"\n"+
							" }"                                                                   
							,
							"gcc"
							,
							"OK"
							,
				},
				//////////////////////////1//////////////////////////////////////////////
				{//多重复杂结构，暂时还不能解决
					"#include <stdlib.h>  "                                                +"\n"+
							"    typedef struct list {"                                            +"\n"+
							"        char * next;"                                                 +"\n"+
							"      } list;"                                                        +"\n"+
							"      typedef struct z {"                                             +"\n"+
							"        list l;"                                                      +"\n"+
							"      } z;"                                                           +"\n"+
							"  "                                                                   +"\n"+
							"      void a6(){ // 2"                                             +"\n"+
							"        z * x =(z*) malloc(sizeof(z));"                               +"\n"+
							"       if (!x) return;//defect"                                               +"\n"+
							"       x->l.next=0;"                                                  +"\n"+
							"       free(x->l.next); "                                     +"\n"+
							"     }"                                                               
							,
							"gcc"
							,
							"OK"
							,
				},
				////////////////////////2/////////////////////////////////////////////
				{
							"typedef struct sa {"                                                  +"\n"+
							"	int a;"                                                              +"\n"+
							"} SA;"                                                                +"\n"+
							""                                                                     +"\n"+
							"int func2() {"                                                        +"\n"+
							"    SA sa;"                                                           +"\n"+
							"    (&sa)->a = (void *)0;  //FP,UVF"                                  +"\n"+
							"    if (sa.a == (void*)0) {"                                          +"\n"+
							"    	return 1;"                                                       +"\n"+
							"		}    "                                                              +"\n"+
							"    return 0;"                                                        +"\n"+
							"}"                                     
							,
							"gcc"
							,
							"OK"
							,
				},	
/////////////////////////////////////3/////////////////////////
				{
					"typedef struct {"                                                     +"\n"+
							"	int i;"                                                              +"\n"+
							"	int j;"                                                              +"\n"+
							"}Test;"                                                               +"\n"+
							"void test1(){"                                                        +"\n"+
							"	Test a,b;"                                                           +"\n"+
							"	b.i=a.j;//DEFECT, UVF, a.j"                                            +"\n"+
							"	a.i=b.j; "                                                           +"\n"+
							"}"  
							,
							"gcc"
							,
							"UVF_Exp"
							,
				},		
/////////////////////////4/////////////////////////////////////////////
				{
							"#include<stdio.h>"                             +"\n"+
							"#include<memory.h>"                             +"\n"+
							"#include<string.h>"                             +"\n"+
							"typedef struct sa {"                                                  +"\n"+
							"	int a;"                                                              +"\n"+
							"} SA;"                                                                +"\n"+
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
/////////////////////////5/////////////////////////////////////////////
				{//多级复杂结构
					"  #include<stdlib.h>"                                                 +"\n"+
							" typedef struct {"                                                    +"\n"+
							"    int x;"                                                           +"\n"+
							"    int y;"                                                           +"\n"+
							"  } S1;"                                                              +"\n"+
							"  "                                                                   +"\n"+
							"  typedef struct {"                                                   +"\n"+
							"    S1* ptr;"                                                         +"\n"+
							"   int z;"                                                            +"\n"+
							" } S2;"                                                               +"\n"+
							" "                                                                    +"\n"+
							" void fun1(S1* local_ptr) {"                                          +"\n"+
							"   int k = local_ptr->x;"                                             +"\n"+
							" }"                                                                   +"\n"+
							" "                                                                    +"\n"+
							" int main() {"                                                        +"\n"+
							"   S2* main_ptr = (S2*)malloc(100);"                                  +"\n"+
							"   if(main_ptr != NULL) {"                                            +"\n"+
							"     fun1(main_ptr->ptr); //DEFECT"                                   +"\n"+
							"     free(main_ptr);"                                                 +"\n"+
							"   }"                                                                 +"\n"+
							"   return 0;"                                                         +"\n"+
							" }"                                                                   
							,
							"gcc"
							,
							"OK"
							,
							},		
////////////////////////////  6  ///////////////////////////////////
	            {
	            "struct s{"                                                            +"\n"+
	            "	int a;"                                                              +"\n"+
	            "	int b;"                                                              +"\n"+
	            "};"                                                                   +"\n"+
	            ""                                                                     +"\n"+
	            "int main(){"                                                          +"\n"+
	            "	struct s x;"                                                         +"\n"+
	            "	x.b=0;"                                                              +"\n"+
	            "	return x.a;//defect,UVF_Exp,x.a"                                     +"\n"+
	            "}"                                                                 
				,
				"gcc"
				,
				"UVF_Exp"
				,
				},	
/////////////////  7   ///////////////////	
	            {
	            "#include <stdlib.h>  "                                                +"\n"+
	            "struct s {"                                                           +"\n"+
	            "    int i;"                                                           +"\n"+
	            "  };"                                                                 +"\n"+
	            "void f(struct s *v, int t) {"                                          +"\n"+
	            " struct s *mm;"                                                           +"\n"+
	            "	mm = v;"                                                             +"\n"+
	            "	t=mm->i;"                                                        +"\n"+
	            " }"                                                                   
	            ,
	            "gcc"
	            ,
	            "OK"
	            ,
	            },
/////////////////  8   ///////////////////	
	            {
	            "#include <stdlib.h>  "                                                +"\n"+
	            "struct s {"                                                           +"\n"+
	            "    int i;"                                                           +"\n"+
	            "  };"                                                                 +"\n"+
	            "int f(struct s *v, int i) {"                                          +"\n"+
	            " struct s mm;"                                                            +"\n"+
	            "	mm.i = i;"                                                           +"\n"+
	            "	return 0;"                                                           +"\n"+
	            " }"                                                                   
	            ,
	            "gcc"
	            ,
	            "OK"
	            ,
	            },
//////////////////////////9//////////////////////////////////////////////
				{//UVF_Exp故障
					"struct s {"                                                           +"\n"+
							"    int a;"                                                           +"\n"+
							"    int b;"                                                           +"\n"+
							"  };"                                                                 +"\n"+
							"  int main() {"                                                       +"\n"+
							"    struct s x;"                                                      +"\n"+
							"    x.b = 0;"                                                         +"\n"+
							"    return x.a; //defect"                                             +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"UVF_Exp"
							,
				},
		});
	}
}


