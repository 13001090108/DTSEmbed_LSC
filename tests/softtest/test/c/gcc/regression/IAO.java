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
public class IAO extends ModelTestBase{
	public IAO(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/IAO-0.1.xml";
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
		            "void f()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "int i;"                                                               +"\n"+
		            "int n=1;"                                                             +"\n"+
		            "int nn=0;"                                                            +"\n"+
		            "int mm=0;"                                                            +"\n"+
		            "for(i=0;i<n;i++)"                                                     +"\n"+
		            "{"                                                                    +"\n"+
		            "++nn;"                                                                +"\n"+
		            "}"                                                                    +"\n"+
		            "mm/=nn;"                                                              +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },

	/////////////////  1   ///////////////////	
		            {
		            "#include <assert.h>"                                                  +"\n"+
		            "void ghx_iao_2_f2()"                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "int p;"                                                               +"\n"+
		            "int f;"                                                               +"\n"+
		            " if(f<=0) return;//assert(f>0);"                                                         +"\n"+
		            "if(p/f>=100)//FP"                                                     +"\n"+
		            "p=f*99;"                                                              +"\n"+
		            "return;"                                                              +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  2   ///////////////////	
		            {
		            "#include <math.h>"                                                    +"\n"+
		            "int ghx_iao_3_f3()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	double a = 10;"                                                      +"\n"+
		            "	double b = log(a - 20);//DEFECT"                                     +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "IAO"
		            ,
		            },
	/////////////////  3   ///////////////////	
		            {
		            "#include <math.h>"                                                    +"\n"+
		            "int ghx_iao_4_f4()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	double a = 0;"                                                       +"\n"+
		            "    fmod(10.0, a);//DEFECT"                                           +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "IAO"
		            ,
		            },
	/////////////////  4   ///////////////////	
		            {
		            "#include <math.h>"                                                    +"\n"+
		            "int ghx_iao_5_f5()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	double a = 10;"                                                      +"\n"+
		            "	double b = acos(a);//DEFECT"                                         +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "IAO"
		            ,
		            },
	/////////////////  5   ///////////////////	
		            {
		            "#include <math.h>"                                                    +"\n"+
		            "int ghx_iao_6_f6()"                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "double c=10;"                                                         +"\n"+
		            "double d=asin(c);//DEFECT"                                            +"\n"+
		            "return 0;"                                                            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "IAO"
		            ,
		            },

		        	/////////////////  6   ///////////////////	
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
		            "   int a=0; s1.i=a;"                                                          +"\n"+	
		            "   int a=1/s1.i;"                                                     +"\n"+

		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "IAO"
		            ,
		            },
		            

		 });
	 }
}
