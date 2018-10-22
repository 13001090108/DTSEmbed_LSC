package fault;


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
public class NPD extends ModelTestBase {
	public NPD(String source,String compiletype, String result)
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
	/////////////////  1   ///////////////////	
		            {
		            "void npd_gen_must(){"                                                 +"\n"+
		            "	int *p = 0;"                                                         +"\n"+
		            "	*p = 1; // NPD"                                                      +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },
		            

	/////////////////  2   ///////////////////	
		            {
		            "typedef struct _ST {"                                                 +"\n"+
		            "	char a;"                                                             +"\n"+
		            "}ST;"                                                                 +"\n"+
		            "int func1(ST* st)"                                                    +"\n"+
		            "{"                                                                    +"\n"+
		            "	ST *sa = NULL;"                                                      +"\n"+
		            "	sa->a = 'a';  //DEFECT,NPD,sa"                                       +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },
		 
		
	/////////////////  3   ///////////////////	
		            {
		            "void xstrcpy(char *dst, char *src){"                                  +"\n"+
		            "	if (!src) return;"                                                   +"\n"+
		            "	dst[0] = src[0]; // NPD"                                             +"\n"+
		            "}"                                                                    +"\n"+
		            "void npd_gen_must(int flag, char *arg){"                              +"\n"+
		            "	char *p = arg;"                                                      +"\n"+
		            "	if (flag) p = 0;"                                                    +"\n"+
		            "	if (arg) {;}"                                                        +"\n"+
		            "	xstrcpy(p,\"Hello\"); // NPD"                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },
	 
		            
	/////////////////  4   ///////////////////	
		            {
		            "int main()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "	int i=0,*p = 0, *q = 0, *a = 0;"                                     +"\n"+
		            "	int j = (p == 0)? i: *p;"                                            +"\n"+
		            "	if(i != 0 || *q > 0)  //DEFECT,NPD,q"                                +"\n"+
		            "	{"                                                                   +"\n"+
		            "		j = 0;"                                                             +"\n"+
		            "	}"                                                                   +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },
	            
	/////////////////  5   ///////////////////	
		            {
		            "void npd_check_must(){"                                               +"\n"+
		            "	char *p = getSomeValue();"                                           +"\n"+
		            "	if (p != (void*)0) { }"                                              +"\n"+
		            "	p[0] = 0;// NPD"                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },

	/////////////////  6   ///////////////////	
		            {
		            "int test1(int level)"                                                 +"\n"+
		            "{"                                                                    +"\n"+
		            "	int* x = NULL;"                                                      +"\n"+
		            "	int p = 0;"                                                          +"\n"+
		            "	if (level>0) {"                                                      +"\n"+
		            "		x=&p;"                                                              +"\n"+
		            "	}"                                                                   +"\n"+
		            "	if (level<4)"                                                        +"\n"+
		            "		return *x; //DEFECT,NPD,x"                                          +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },
	  
		            
	/////////////////  7   ///////////////////	
		            {
		            "int test2(int b){"                                                    +"\n"+
		            "	int* x = NULL;"                                                      +"\n"+
		            "	if (b)"                                                              +"\n"+
		            "		x =(int *)malloc(8);"                                               +"\n"+
		            "	if (!b)"                                                             +"\n"+
		            "		return *x;   //DEFECT,NPD,x"                                        +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },

		
	/////////////////  8   ///////////////////	
		            {
		            "typedef struct _st{"                                                  +"\n"+
		            "	int a;"                                                              +"\n"+
		            "}ST;"                                                                 +"\n"+
		            "void test1(ST* st, int c){"                                           +"\n"+
		            "	int b;"                                                              +"\n"+
		            "	if (st == 0 || c ==1) {"                                             +"\n"+
		            "		b = (*st).a;  //DEFECT,NPD,st"                                      +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },
		            
	/////////////////  9   ///////////////////	
		            {
		            "int *g(){"                                                            +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            "int f2(){"                                                            +"\n"+
		            "	int *t=g();"                                                         +"\n"+
		            "	if(1>0 && *t>0){ //DEFECT,NPD, t"                                    +"\n"+
		            "		return false;"                                                      +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },
		            
	/////////////////  10   ///////////////////	
		            {
		            "void f(int* p,int* q){"                                               +"\n"+
		            "	if(q!=(void*)0){"                                                    +"\n"+
		            "		return;"                                                            +"\n"+
		            "	}"                                                                   +"\n"+
		            "	if(p==q){"                                                           +"\n"+
		            "		int b;"                                                             +"\n"+
		            "	}"                                                                   +"\n"+
		            "	int a=*p;	//DEFECT,NPD,p"                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },

	/////////////////  11   ///////////////////	
		            {
		            "int *getNull(){"                                                      +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            "void npd_gen_must(int flag, char *arg){"                              +"\n"+
		            "	int *p = getNull();"                                                 +"\n"+
		            "	*p = 1; // NPD"                                                      +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },
	            
	
	/////////////////  12   ///////////////////	
		            {
		            "int *func() {"                                                        +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            "int func1()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	int *p;"                                                             +"\n"+
		            "	p = func();"                                                         +"\n"+
		            "	*p = 1;  //DEFECT,NPD,p"                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },
		            
	/////////////////  13   ///////////////////	
		            {
		            "void f(){"                                                            +"\n"+
		            "	g(h());  //DEFECT,NPD,The 1 Param of function g"                     +"\n"+
		            "}"                                                                    +"\n"+
		            "void g(int* p){"                                                      +"\n"+
		            "	int a=*p;  //FP,NPD"                                                 +"\n"+
		            "}"                                                                    +"\n"+
		            "int* h(){"                                                            +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },


	/////////////////  14   ///////////////////	
		            {
		            ""                                                                     
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },
		            
		            
	/////////////////  15   ///////////////////	
		            {
		            "void test18_1(int flag,char* to)"                                     +"\n"+
		            "{"                                                                    +"\n"+
		            "	char *s;"                                                            +"\n"+
		            "	s=(char *)malloc(sizeof(8));"                                        +"\n"+
		            "	read(1,s,sizeof(s));  //DEFECT,NPD,s "                               +"\n"+
		            "	free(s);"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },

	/////////////////  16   ///////////////////	
		            {
		            "int *p;"                                                              +"\n"+
		            "void f1()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	p = 0;"                                                              +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	f1();"                                                               +"\n"+
		            "	*p = 5;     "                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "NPD"
		            ,
		            },
	
		 });
	 }
}
