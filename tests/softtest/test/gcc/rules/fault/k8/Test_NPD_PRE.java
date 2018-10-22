package softtest.test.gcc.rules.fault.k8;

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
public class Test_NPD_PRE extends ModelTestBase {
	public Test_NPD_PRE(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/NPD_PRE-0.1.xml";
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
		            ""                                                                     +"\n"+
		            "static int a;"                                                        +"\n"+
		            ""                                                                     +"\n"+
		            "int* getValue(void)  {return (int*)malloc(sizeof(int));}"                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void reassign(int *argument, int *p) {"                               +"\n"+
		            "        	*argument = *p;"                                             +"\n"+
		            "}"                                                                    +"\n"+
		            "void npd_check_call_might(int *argument) {"            +"\n"+
		            "    	int *p = getValue();"                                            +"\n"+
		            "    	if (p != 0) {"                                                   +"\n"+
		            "      		*p = 1;"                                                      +"\n"+
		            "    	}"                                                               +"\n"+
		            "        	reassign(argument, p);   "                           +"\n"+
		            "}"                                                                   
		            ,
		            "gcc"
		            ,
		            "NPD_PRE"
		            ,
		            },

	/////////////////  1   ///////////////////	
		            {
		            "static int a;"                                                        +"\n"+
		            "int goodEnough(int *a) {return 1;}"                                   +"\n"+
		            "int* getValue(void)  {return &a;}"                                    +"\n"+
		            "void reassign(int *argument, int *p) {"                               +"\n"+
		            "    			if (goodEnough(argument)) return;"                             +"\n"+
		            "    			*argument = *p;"                                               +"\n"+
		            "}"                                                                    +"\n"+
		            " 			void npd_check_call_must(int *argument) {"                        +"\n"+
		            "    			int *p = getValue();"                                          +"\n"+
		            "    			if (p != 0) {"                                                 +"\n"+
		            "      				*p = 1;"                                                    +"\n"+
		            "    			}"                                                             +"\n"+
		            "    			reassign(argument, p);   //OK"                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },            
	/////////////////  2   ///////////////////	
		            {
		            "#include<stdio.h>"                                                    +"\n"+
		            "static char a;"                                                       +"\n"+
		            "char* getSomeValue(void)  {return &a;}"                               +"\n"+
		            "void xstrcpy(char *dst, char *src) {"                                 +"\n"+
		            "    			if (!src) return;"                                             +"\n"+
		            "    			dst[0] = src[0];"                                              +"\n"+
		            "}"                                                                    +"\n"+
		            "void npd_check_might(char *arg) {"                                    +"\n"+
		            "    			char *p = getSomeValue();"                                     +"\n"+
		            "    			if (p != NULL) {  }"                                           +"\n"+
		            "    			if (arg) { p = arg; }"                                         +"\n"+
		            "    			xstrcpy(p, \"Hello\");   //OK"                               +"\n"+
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
