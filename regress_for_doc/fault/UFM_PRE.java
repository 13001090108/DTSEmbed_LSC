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
public class UFM_PRE extends ModelTestBase {
	public UFM_PRE(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/UFM_PRE-0.1.xml";
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
		            "#include <stdlib.h>   "                                               +"\n"+
		            "typedef struct x {    "                                               +"\n"+
		            "	char * field;     "                                                  +"\n"+
		            "} tx;                                       "                         +"\n"+
		            "void release(tx * a){ "                                               +"\n"+
		            "	a->field = \"ab\";          "                                          +"\n"+
		            "}                                            "                        +"\n"+
		            "int main() {           "                                              +"\n"+
		            "	tx *a = (tx *)malloc(sizeof(tx));"                                   +"\n"+
		            "	if (a==0) return;  "                                                 +"\n"+
		            "	a->field = (char *)malloc(10); "                                     +"\n"+
		            "	free(a);       "                                                     +"\n"+
		            "	release(a);        "                                                 +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM_PRE"
		            ,
		            },

	/////////////////  2   ///////////////////	
		            {
		            "#include <stdlib.h>   "                                               +"\n"+
		            "int* p;                 "                                             +"\n"+
		            "void f(){               "                                             +"\n"+
		            "	*p=1;                 "                                              +"\n"+
		            "}                       "                                             +"\n"+
		            "void f1(){              "                                             +"\n"+
		            "    f();               "                                              +"\n"+
		            "}                       "                                             +"\n"+
		            "void f2(){              "                                             +"\n"+
		            "   p=(int*)malloc(1);   "                                             +"\n"+
		            "   free(p);             "                                             +"\n"+
		            "   f1(); //defect       "                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM_PRE"
		            ,
		            },


		 });
	 }
}
