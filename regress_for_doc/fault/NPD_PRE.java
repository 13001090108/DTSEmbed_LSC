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
public class NPD_PRE extends ModelTestBase {
	public NPD_PRE(String source,String compiletype, String result)
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


		/////////////////  1   ///////////////////	
			            {
			            "int func5(int *a){"                                                   +"\n"+
			            "	*a = 1;"                                                             +"\n"+
			            "	return 0;"                                                           +"\n"+
			            "}"                                                                    +"\n"+
			            "int main()"                                                           +"\n"+
			            "{"                                                                    +"\n"+
			            "	int a = 1;"                                                          +"\n"+
			            "	int* p;"                                                             +"\n"+
			            "	p = NULL;"                                                           +"\n"+
			            "	func5(p);  //DEFECT, NPD,p"                                          +"\n"+
			            "	return 0;"                                                           +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "NPD_PRE"
			            ,
			            },

		/////////////////  2   ///////////////////	
			            {
			            "int func5(int *a){"                                                   +"\n"+
			            "	*a = 1;"                                                             +"\n"+
			            "	return 0;"                                                           +"\n"+
			            "}"                                                                    +"\n"+
			            "int func6(int* b) {"                                                  +"\n"+
			            "	return func5(b);"                                                    +"\n"+
			            "}"                                                                    +"\n"+
			            "int main()"                                                           +"\n"+
			            "{"                                                                    +"\n"+
			            "	int a = 1;"                                                          +"\n"+
			            "	int* p;"                                                             +"\n"+
			            "	p = NULL;"                                                           +"\n"+
			            "	func6(p);  //DEFECT, NPD,p"                                          +"\n"+
			            "	return 0;"                                                           +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "NPD_PRE"
			            ,
			            },
	
		/////////////////  3   ///////////////////	
			            {
			            "int* h(){"                                                            +"\n"+
			            "	return NULL;"                                                        +"\n"+
			            "}"                                                                    +"\n"+
			            "void g1(int* p){"                                                     +"\n"+
			            "	if(p==(void*)0&&*p==0){  //FP, NPD"                                  +"\n"+
			            "		return;"                                                            +"\n"+
			            "	}"                                                                   +"\n"+
			            "}"                                                                    +"\n"+
			            "void f(){"                                                            +"\n"+
			            "	g1(h());//DEFECT, NPD,The 1 Param of function g1"                    +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "NPD_PRE"
			            ,
			            },

		/////////////////  4   ///////////////////	
			            {
			            "int* h(){"                                                            +"\n"+
			            "	return NULL;"                                                        +"\n"+
			            "}"                                                                    +"\n"+
			            "void g2(int* p){"                                                     +"\n"+
			            "	if(!p&&*p==0){  //FP, NPD"                                           +"\n"+
			            "		return;"                                                            +"\n"+
			            "	}"                                                                   +"\n"+
			            "}"                                                                    +"\n"+
			            "void f(){"                                                            +"\n"+
			            "	g2(h());//DEFECT, NPD,The 1 Param of function g2"                    +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "NPD_PRE"
			            ,
			            },
		/////////////////  5   ///////////////////	
			            {
			            "int *p;"                                                              +"\n"+
			            "int f()"                                                              +"\n"+
			            "{"                                                                    +"\n"+
			            "	*p;"                                                                 +"\n"+
			            "}"                                                                    +"\n"+
			            "int g()"                                                              +"\n"+
			            "{"                                                                    +"\n"+
			            "	f();"                                                                +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"
			            ,
			            "NPD_PRE"
			            ,
			            },
     


		 });
	 }
}
