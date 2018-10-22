package softtest.test.c.gcc.regression;

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
public class IAO_PRE extends ModelTestBase{
	public IAO_PRE(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}
	
	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/IAO_PRE-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("fault");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
		
		//加载库函数摘要
		LIB_SUMMARYS_PATH="gcc_lib/lib_summary.xml";
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
		            "int func2(int, int, int);"                                            +"\n"+
		            "int func3(int, int);"                                                 +"\n"+
		            ""                                                                     +"\n"+
		            "void func1(int flag, int a, int b)"                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (a > 2 && a < 10) {"                                              +"\n"+
		            "		func2(flag, a, b);"                                                 +"\n"+
		            "	} else {"                                                            +"\n"+
		            "		func2(flag, a, b); //DEFECT"                                        +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int func2(int flag, int var1, int var2)"                              +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (flag > 0) {"                                                     +"\n"+
		            "		return var2 % var1;"                                                +"\n"+
		            "	} else {"                                                            +"\n"+
		            "		return func3(var1, var2);"                                          +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int func3(int var1, int var2)"                                        +"\n"+
		            "{"                                                                    +"\n"+
		            "	var2 /= var1;"                                                       +"\n"+
		            "	return var2;"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "IAO_PRE"
		            ,
		            },
	/////////////////  1   ///////////////////	
		            {
		            "#include <math.h>"                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int func2(int, int);"                                                 +"\n"+
		            "int func3(int);"                                                      +"\n"+
		            ""                                                                     +"\n"+
		            "void func1(int flag, int a)"                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (a >= -1 && a <= 1) {"                                            +"\n"+
		            "		func2(flag, a);"                                                    +"\n"+
		            "	} else {"                                                            +"\n"+
		            "		func2(flag, a); //DEFECT"                                           +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int func2(int flag, int var1)"                                        +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (flag > 0) {"                                                     +"\n"+
		            "		return acos(var1);"                                                 +"\n"+
		            "	} else {"                                                            +"\n"+
		            "		return func3(var1);"                                                +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int func3(int var1)"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	return acos(var1);"                                                  +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "IAO_PRE"
		            ,
		            },
	/////////////////  2   ///////////////////	
		            {
		            "#include <math.h>"                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func1(int var)"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	func2(var);"                                                         +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int func2(int var)"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (var < 0) {"                                                      +"\n"+
		            "		return func3(var); //DEFECT"                                        +"\n"+
		            "	} else {"                                                            +"\n"+
		            "		return 0;"                                                          +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int func3(int var)"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	return sqrt(var);"                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "IAO_PRE"
		            ,
		            },
	/////////////////  3   ///////////////////	
		            {
		            "int jhb_iao_2_f1(int t){"                                             +"\n"+
		            "		int x=10;"                                                          +"\n"+
		            "		return (x/t);"                                                      +"\n"+
		            "		"                                                                   +"\n"+
		            "	}"                                                                   +"\n"+
		            "void jhb_iao_2_f2(){"                                                 +"\n"+
		            "		int i;"                                                             +"\n"+
		            "		i=jhb_iao_2_f1(0);   //DEFECT"                                      +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "IAO_PRE"
		            ,
		            },
	/////////////////  4   ///////////////////	
		            {
		            "int func2(int);"                                                      +"\n"+
		            "int func3();"                                                         +"\n"+
		            ""                                                                     +"\n"+
		            "void func1(int var, int flag)"                                        +"\n"+
		            "{"                                                                    +"\n"+
		            "	int i;"                                                              +"\n"+
		            ""                                                                     +"\n"+
		            "	i = var / func2(flag); //DEFECT"                                     +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int func2(int flag)"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "	if (flag < 0) {"                                                     +"\n"+
		            "		return func3();"                                                    +"\n"+
		            "	} else {"                                                            +"\n"+
		            "		return 0;"                                                          +"\n"+
		            "	}"                                                                   +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int func3()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  5   ///////////////////	
		            {
		            "#include <stdio.h>"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "struct S{"                                                            +"\n"+
		            "   char a[12];"                                                       +"\n"+
		            "   char b[34];"                                                       +"\n"+
		            "   int i;"                                                            +"\n"+
		            "}s1;"                                                                 +"\n"+
		            ""                                                                     +"\n"+
		            "void f(){"                                                            +"\n"+
		            "int b=1/a;   int a=1/s1.i;"                                                     +"\n"+
		            "}"                                                                    +"\n"+
		            "void f1(){"                                                           +"\n"+
		            "   f();"                                                              +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2(){"                                                           +"\n"+
		            "   int a=0;"                                                          +"\n"+
		            "   s1.i=a;"                                                           +"\n"+
		            "   f1();"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "IAO_PRE"
		            ,
		            },
		        	/////////////////  6   ///////////////////	
		            {
			        "#include <math.h>"                                                    +"\n"+
			        ""                                                                     +"\n"+
			        "int g_val1 = 0;"                                                      +"\n"+
			        "int g_val2 = 0;"                                                      +"\n"+
			        ""                                                                     +"\n"+
		            "void func2();"                                                        +"\n"+
		            "double func3();"                                                         +"\n"+
		            ""                                                                     +"\n"+			            
		            "void func1()"                                                         +"\n"+
			        "{"                                                                    +"\n"+
			        "	double i=func3();"                                                            +"\n"+
			        "	func2();"                                                            +"\n"+
		            "	double j=func3();"                                                            +"\n"+
			        "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "void func2()"                                                         +"\n"+
		            "{"                                                                    +"\n"+
		            "	g_val1 = g_val2 = 0;"                                                +"\n"+			            "}"                                                                    +"\n"+
			        ""                                                                     +"\n"+
			        "double func3()"                                                          +"\n"+
		            "{"                                                                    +"\n"+
		            "	return g_val1/g_val2; //false"                              +"\n"+
		            "}"                                                                    
		            ,
			        "gcc"
			        ,
			        "IAO_PRE"
		            ,
		            },
	/////////////////  7  ///////////////////	
		            {
		            "int f(){"                                                             +"\n"+
		            "   return 0;"                                                         +"\n"+
		            "}"                                                                    +"\n"+
		            "void f1(int i){"                                                      +"\n"+
		            "   int j=1/i;"                                                        +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2(){"                                                           +"\n"+
		            "   f1(f()); "                                                         +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "IAO_PRE"
		            ,
		            },

		            
		 });
	 }
}
