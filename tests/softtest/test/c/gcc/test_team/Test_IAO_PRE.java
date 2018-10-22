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
public class Test_IAO_PRE extends ModelTestBase{
	public Test_IAO_PRE(String source,String compiletype, String result)
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
		            "void f(int i){"                                                       +"\n"+
		            "   int j=1/i;"                                                        +"\n"+
		            "}"                                                                    +"\n"+
		            "void f1(){"                                                           +"\n"+
		            "   int i=0;"                                                          +"\n"+
		            "   f(i);//DEFECT"                                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "IAO_PRE"
		            ,
		            },
/////////////////  1   ///////////////////	
		            {
		            "void f(int i){"                                                       +"\n"+
		            "   int j=1/i;"                                                        +"\n"+
		            "}"                                                                    +"\n"+
		            "void f1(int i){"                                                      +"\n"+
		            "   "                                                                  +"\n"+
		            "   f(i);"                                                             +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2(){"                                                           +"\n"+
		            "   int i=0;"                                                          +"\n"+
		            "   f1(i); //defect"                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "IAO_PRE"
		            ,
		            },
/////////////////  2  zys:2011.6.24	 原来的测试用例本身就有错啊！！！///////////////////	
		            {
		            "int i;"                                                               +"\n"+
		            "void f(){"                                                            +"\n"+
		            "   int j=1/i;"                                                        +"\n"+
		            "}"                                                                    +"\n"+
		            "void f1(){"                                                           +"\n"+
		            "   "                                                                  +"\n"+
		            "   f();"                                                             +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2(){"                                                           +"\n"+
		            "   i=0;"                                                              +"\n"+
		            "   f1(); //defect"                                                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "IAO_PRE"
		            ,
		            },
/////////////////  3   ///////////////////	
		            {
		            "int i;"                                                               +"\n"+
		            "void f(){"                                                            +"\n"+
		            "   int j=1/i;"                                                        +"\n"+
		            "}"                                                                    +"\n"+
		            "void f1(){"                                                           +"\n"+
		            "   "                                                                  +"\n"+
		            "   if(i)"                                                             +"\n"+
		            "      f(i);"                                                          +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2(){"                                                           +"\n"+
		            "   i=0;"                                                              +"\n"+
		            "   f1(i); //ok"                                                       +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
/////////////////  4  ///////////////////	
		            {
		            "void f(int i){"                                                       +"\n"+
		            "   int j=1/i;"                                                        +"\n"+
		            "}"                                                                    +"\n"+
		            "void f1(int i){"                                                      +"\n"+
		            "   "                                                                  +"\n"+
		            "   if(i)"                                                             +"\n"+
		            "      f(i);"                                                          +"\n"+
		            "}"                                                                    +"\n"+
		            "void f2(){"                                                           +"\n"+
		            "   int i=0;"                                                          +"\n"+
		            "   f1(i); //ok"                                                       +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
/////////////////  5   ///////////////////	
		            {
		            "void f(int i){"                                                       +"\n"+
		            "   int j=1/i; "                                                       +"\n"+
		            "}"                                                                    +"\n"+
		            "void f1(int i){"                                                      +"\n"+
		            "   f(i);"                                                             +"\n"+
		            "}"                                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int f2(){"                                                            +"\n"+
		            "   return 0;"                                                         +"\n"+
		            "}"                                                                    +"\n"+
		            "void f3(){"                                                           +"\n"+
		            "   f1(f2());//defect"                                                 +"\n"+
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
