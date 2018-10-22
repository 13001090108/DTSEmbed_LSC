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
public class Test_NPD extends ModelTestBase {
	public Test_NPD(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/NPD-0.1.xml";
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
	/////////////////  0   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include <stdlib.h>"                                                  +"\n"+
		            "void func(int *s)"                                                    +"\n"+
		            "{"                                                                    +"\n"+
		            "    int i;"                                                           +"\n"+
		            "    for(i=0;i<10;i++)"                                                +"\n"+
		            "    s[i]=i+1;"                                                        +"\n"+
		            "	"                                                                    +"\n"+
		            "}"                                                                    +"\n"+
		            "int main(int argc, char *argv[])"                                     +"\n"+
		            "{"                                                                    +"\n"+
		            "  int *p;"                                                            +"\n"+
		            "  int a[10];"                                                         +"\n"+
		            "  int i;"                                                             +"\n"+
		            "  p=(int *)malloc(10);"                                               +"\n"+
		            "  func(p);"                                                           +"\n"+
		            "  for(i=0;i<10;i++)"                                                  +"\n"+
		            "  {"                                                                  +"\n"+
		            "    a[i]=p[i];"                                                       +"\n"+
		            "  } "                                                                 +"\n"+
		            "  printf(\"%d\",a[0]);"                                                 +"\n"+
		            "  free(p);"                                                           +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,                                                       
		            "NPD"           
		         
		            ,
		            },
			 
		
	/////////////////  1   ///////////////////	
		        

	/////////////////  2  ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "#include<stdlib.h>"                                                   +"\n"+
		            "struct Student"                                                       +"\n"+
		            "{"                                                                    +"\n"+
		            "  int age;"                                                           +"\n"+
		            "};"                                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "struct Student *func2()"                                              +"\n"+
		            "{"                                                                    +"\n"+
		            "  struct Student *r;"                                                 +"\n"+
		            "   if((r=(struct Student *)malloc(sizeof(struct Student)))==NULL)"    +"\n"+
		            "     return NULL;"                                                    +"\n"+
		            "   else "                                                             +"\n"+
		            "     return r;"                                                       +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int main()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "  struct Student *r;"                                                 +"\n"+
		            "  r=func2();"                                                         +"\n"+
		            " r->age=1;"                                                           +"\n"+
		            "  return 0;"                                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,                                                       
		            "NPD"           
		         
		            ,
		            },

	/////////////////  0   ///////////////////	
		            {
		            "int main()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "	int i=0,*q ;"                                     +"\n"+
		            "q= (int *)calloc(16);"                                                                     +"\n"+
		            "	if(*q > 0)  //DEFECT,NPD,q"                                +"\n"+
		            "	{"                                                                   +"\n"+
		            "		i = 0;"                                                             +"\n"+
		            "	}"                                                                   +"\n"+
		            "	return i;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },
	/////////////////  1   ///////////////////	
		            {
		            "void func4() {"                                                       +"\n"+
		            "	void *ptr = (void*)0;"                                               +"\n"+
		            "	char* net = (char*)ptr;"                                             +"\n"+
		            "	*net = '1';  //DEFECT,NPD,net"                                       +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },
	/////////////////  2   ///////////////////	
		            {
		            "void func2(void* ptr) {"                                              +"\n"+
		            "	char* net = (char*)ptr; //FP,NPD"                                    +"\n"+
		            "	*net = '1'; //DEFECT,NPD"                                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  3   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "typedef struct _ST {"                                                 +"\n"+
		            "    char a;"                                                          +"\n"+
		            "}ST;"                                                                 +"\n"+
		            "int func1(ST* st)"                                                    +"\n"+
		            "{"                                                                    +"\n"+
		            "    ST *sa = (void*)0;"                                               +"\n"+
		            "    sa->a = 'a';  //DEFECT,NPD,sa"                                    +"\n"+
		            "    return 0;"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },
	/////////////////  4   ///////////////////	
		            {
		            "typedef struct _ST {"                                                 +"\n"+
		            "    char a;"                                                          +"\n"+
		            "}ST;"                                                                 +"\n"+
		            "int func(ST* st)"                                                     +"\n"+
		            "{"                                                                    +"\n"+
		            "    ST *sa = (ST*)st;"                                                +"\n"+
		            "    if (sa == ((void *)0) || sa->a == 'w') { //FP,NPD"                +"\n"+
		            "       return 1;"                                                     +"\n"+
		            "    }"                                                                +"\n"+
		            "    return 0;"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  5   ///////////////////	
		            {
		            ""                                                                     +"\n"+
		            "int func5(int *a){"                                                   +"\n"+
		            "	*a = 1;  //FP,NPD"                                                   +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            "int main()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "	int a = 1;"                                                          +"\n"+
		            "	int* p;"                                                             +"\n"+
		            "	p = &a;"                                                             +"\n"+
		            "	func5(p);"                                                           +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  6   ///////////////////	
		            {
		            "void func4()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	int* p;"                                                             +"\n"+
		            "	int* a = 0;"                                                         +"\n"+
		            "	p = a;"                                                              +"\n"+
		            "	p[0] = 1;  //DEFECT,NPD,p"                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },
		        	/////////////////  7  ///////////////////	
		            {
		            "int func8(int *b) {"                                                   +"\n"+
		            "	int *a = b;"                                                   +"\n"+
		            "   if (a != (void*)0) {"                                                +"\n"+
		            "		*a = 1;  //FP,NPD"                                                  +"\n"+
		            "	}"                                                                   +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    +"\n"
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },

	/////////////////  8   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            "typedef struct _ST {"                                                 +"\n"+
		            "    int a;"                                                           +"\n"+
		            "}ST;"                                                                 +"\n"+
		            ""                                                                     +"\n"+
		            "int func(ST* st)"                                                     +"\n"+
		            "{"                                                                    +"\n"+
		            "    ST *sa = (ST*)malloc(sizeof(ST));"                                +"\n"+
		            "    if (sa != NULL ) {"                                        +"\n"+
		            "       sa->a = 1; //FP,NPD"                                           +"\n"+
		            "       return 1;"                                                     +"\n"+
		            "    }"                                                                +"\n"+
		            "    return 0;"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		        	/////////////////  9   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "void zk_npd_31_f1(char *pathname)"                                    +"\n"+
		            "{"                                                                    +"\n"+
		            "	FILE *fp;"                                                           +"\n"+
		            ""                                                                     +"\n"+
		            "	fp = fopen(pathname, \"a\");"                                          +"\n"+
		            "	fprintf(fp, \"Acess file\"); //DEFECT"                                 +"\n"+
		            "	return;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
////////////////	/ 1 0   ///////////////////	
		            {
		            "#include <stdlib.h>"                                                  +"\n"+
		            "int* p;"                                                              +"\n"+
		            "void f(){"                                                            +"\n"+
		            "	 free(p);"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            "void f1(){"                                                           +"\n"+
		            "     f();"                                                            +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2(){"                                                           +"\n"+
		            "   p=(int*)malloc(1);"                                                +"\n"+
		            "   f1(); "                                                            +"\n"+
		            "   *p=1; //defect"                                                    +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },
	/////////////////  11  ///////////////////	
		            {
		            "struct user_data"                                                     +"\n"+
		            "{"                                                                    +"\n"+
		            "    char* s;"                                                         +"\n"+
		            "};"                                                                   +"\n"+
		            "char* f(struct user_data *ud)"                                        +"\n"+
		            "{"                                                                    +"\n"+
		            "   return ud->s; "                                                    +"\n"+
		            "}"                                                                    +"\n"+
		            "void g(struct user_data *ud)"                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "   char* ss = f(ud);"                                                 +"\n"+
		            "   *ss = 'a';"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  12   ///////////////////	
		            {
		            "typedef struct row_desc_tag {"                                        +"\n"+
		            "	int		tInfo;"                                                         +"\n"+
		            "	struct row_desc_tag	*pNext;"                                         +"\n"+
		            "} row_desc_type;"                                                     +"\n"+
		            "void vDestroyRowInfoList(void)"                       +"\n"+
		            "{"                                                                    +"\n"+
		            "	row_desc_type *pCurr, *pNext;"                                               +"\n"+
		            ""                                                                     +"\n"+
		            "	while (pCurr != NULL) {"                                             +"\n"+
		            "		pNext = pCurr->pNext;"                                              +"\n"+
		            "		pCurr = pNext;"                                                     +"\n"+
		            "	}"                                                                   +"\n"+
		            "} "                                                                   
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
		 });
	 }
}
