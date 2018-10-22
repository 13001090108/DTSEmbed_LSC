package softtest.test.android.gcc;

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
	            "#include<stdio.h>"                                                    +"\n"+
	            "#include<stdlib.h>"                                                   +"\n"+
	            "int ext2fs_get_mem(unsigned long size, void *ptr)"                     +"\n"+
	            "{"                                                                    +"\n"+
	            "	void *pp;"                                                           +"\n"+
	            ""                                                                     +"\n"+
	            "	pp = malloc(size);"                                                  +"\n"+
	            "	if (pp == (void*)0)"                                                            +"\n"+
	            "		return 1;"                                                      +"\n"+
	            "	memcpy(ptr, &pp, sizeof (pp));"                                      +"\n"+
	            "   free(pp);"                                                           +"\n"+
	            "	return 0;"                                                           +"\n"+
	            "}"
	            ,
	            "gcc"
	            ,
	            "OK"
	            ,
	            },	
/////////////////  1   ///////////////////	
	            {
	            "#include <stdlib.h>"                                                  +"\n"+
	            "typedef struct{"                                                      +"\n"+
	            "   char* p;"                                                          +"\n"+
	            "} S;"                                                                 +"\n"+
	            "S* func()"                                                            +"\n"+
	            "{"                                                                    +"\n"+
	            "   S* s=(S*)malloc(sizeof(S));"                                       +"\n"+
	            "   s->p=(char*)malloc(11);"                                           +"\n"+
	            "   return s;"                                                         +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "OK"
	            },
/////////////////  2   ///////////////////	
	            {
	            "#include <stdlib.h>"                                                  +"\n"+
	            "typedef struct a{"                                                    +"\n"+
	            "   int data;"                                                         +"\n"+
	            "   struct a * next;"                                                  +"\n"+
	            "} S;"                                                                 +"\n"+
	            "void func2(S* p1,S** p2){"                                            +"\n"+
	            "   *p2 = p1;     "                                                    +"\n"+
	            "}"                                                                    +"\n"+
	            "void func(S* head)"                                                   +"\n"+
	            "{"                                                                    +"\n"+
	            "   S* temp=(S*)malloc(sizeof(S));"                                    +"\n"+
	            "   S* p;"                                                             +"\n"+
	            "   func2(head,&p);"                                                   +"\n"+
	            "   temp->next = p->next;"                                             +"\n"+
	            "   p->next = temp;"                                                   +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "OK"
	            },
/////////////////  3   ///////////////////	
	            {
	            "#include <stdlib.h>"                                                  +"\n"+
	            "typedef struct a{"                                                    +"\n"+
	            "   int data;"                                                         +"\n"+
	            "   struct a * next;"                                                  +"\n"+
	            "} S;"                                                                 +"\n"+
	            "void func(S* head)"                                                   +"\n"+
	            "{"                                                                    +"\n"+
	            "   S* temp=(S*)malloc(sizeof(S));"                                    +"\n"+
	            "   temp->next = head->next;"                                          +"\n"+
	            "   head->next = temp;"                                                +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "OK"
	            },
/////////////////  4   ///////////////////	
	            {
	            "#include <stdlib.h>"                                                  +"\n"+
	            "void func(int flag)"                                                  +"\n"+
	            "{"                                                                    +"\n"+
	            "   int *p;if(flag >128)  "                                                   +"\n"+
	            "       p=(int*)malloc(sizeof(int));"                             +"\n"+
	            "   if(flag >128)"                                                     +"\n"+
	            "       free(p);"                                                      +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "OK"
	            },
/////////////////  5   ///////////////////	
	            {
	            "#include <stdlib.h>"                                                  +"\n"+
	            "void func(int flag)"                                                  +"\n"+
	            "{"                                                                    +"\n"+
	            "   int a[128];"                                                       +"\n"+
	            "   int *p =a;"                                                        +"\n"+
	            "   if(flag >128)  "                                                   +"\n"+
	            "        p=(int*)malloc(sizeof(int));"                             +"\n"+
	            "   if(*p !=a)"                                                        +"\n"+
	            "       free(p);"                                                      +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "OK"
	            },
/////////////////  6   ///////////////////
	            //此误报位于13.mdb中，明明提出来跑没有问题。？？？
	            {
	            "#include <stdlib.h>"                                                  +"\n"+
	            "#define HB_DECLARE_STACKARRAY(Type, Name) \\"                          +"\n"+
	            "    Type stack##Name[512]; \\"                                         +"\n"+
	            "    Type *Name = stack##Name;"                                        +"\n"+
	            ""                                                                     +"\n"+
	            "#define HB_INIT_STACKARRAY(Type, Name, Length) \\"                     +"\n"+
	            "    if ((Length) >= 512) \\"                                           +"\n"+
	            "        Name = (Type *)malloc((Length) * sizeof(Type));"              +"\n"+
	            ""                                                                     +"\n"+
	            "#define HB_STACKARRAY(Type, Name, Length) \\"                          +"\n"+
	            "    HB_DECLARE_STACKARRAY(Type, Name) \\"                              +"\n"+
	            "    HB_INIT_STACKARRAY(Type, Name, Length)"                           +"\n"+
	            ""                                                                     +"\n"+
	            "#define HB_FREE_STACKARRAY(Name) \\"                                   +"\n"+
	            "    if (stack##Name != Name) \\"                                       +"\n"+
	            "        free(Name);"                                                  +"\n"+
	            "void func(){"                                                         +"\n"+
	            "   HB_STACKARRAY(int, shapedChars, 12);"                              +"\n"+
	            "   HB_FREE_STACKARRAY(shapedChars);"                                  +"\n"+
	            "   return;     "                                                      +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "OK"
	            },
/////////////////  7   ///////////////////
	            //问题出现在25.mdb,不知道什么意思
	            {
	            "#include<stdlib.h>"                                                   +"\n"+
	            "int android_log_addFilterString("                                     +"\n"+
	            "        const char *filterString)"                                    +"\n"+
	            "{"                                                                    +"\n"+
	            "    char *filterStringCopy = strdup (filterString);"                  +"\n"+
	            "    char *p_cur = filterStringCopy;"                                  +"\n"+
	            "    free (filterStringCopy);"                                         +"\n"+
	            "    return 0;"                                                        +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "OK"

	            },


		 });
	 }
}