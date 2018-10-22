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
public class UFM extends ModelTestBase  {
	public UFM(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/UFM-0.1.xml";
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
		            "void test1(int b){"                                                   +"\n"+
		            "	int *memleak_error1=NULL;"                                           +"\n"+
		            "	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
		            "	if (b > 0) {"                                                        +"\n"+
		            "		free(memleak_error1);"                                              +"\n"+
		            "	}"                                                                   +"\n"+
		            "	*memleak_error1 = 1;//DEFECT, UFM, memleak_error1"                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM"
		            ,
		            },

	/////////////////  2   ///////////////////	
		            {
		            "void test1(){"                                                        +"\n"+
		            "	int *memleak_error1=NULL;"                                           +"\n"+
		            "	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
		            "	free(memleak_error1);"                                               +"\n"+
		            "	*memleak_error1 = 1;//DEFECT, UFM, memleak_error1"                   +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM"
		            ,
		            },
			 
	/////////////////  3   ///////////////////	
		            {
		            "void func(int* p, int a)"                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "	*p = 1;"                                                             +"\n"+
		            "} "                                                                   +"\n"+
		            "void test2(int b){"                                                   +"\n"+
		            "	int *memleak_error1=NULL;"                                           +"\n"+
		            "	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
		            "	if (b > 0) {"                                                        +"\n"+
		            "		free(memleak_error1);"                                              +"\n"+
		            "	}"                                                                   +"\n"+
		            "	func(memleak_error1, 1);//DEFECT, UFM, memleak_error1"               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM"
		            ,
		            },
	/////////////////  4   ///////////////////	
		            {
		            "int* test3(){"                                                        +"\n"+
		            "	int *memleak_error1=NULL;"                                           +"\n"+
		            "	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
		            "	free(memleak_error1);"                                               +"\n"+
		            "	return memleak_error1;//DEFECT, UFM, memleak_error1"                 +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM"
		            ,
		            },

	/////////////////  5   ///////////////////	
		            {
		            "int* test5(){"                                                        +"\n"+
		            "	int *memleak_error1=NULL;"                                           +"\n"+
		            "	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
		            "	free(memleak_error1);"                                               +"\n"+
		            "	int *p;"                                                             +"\n"+
		            "	p = memleak_error1 + 1;//DEFECT, UFM, memleak_error1"                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM"
		            ,
		            },
	/////////////////  6   ///////////////////	
		            {
		            "int* test4(){"                                                        +"\n"+
		            "	int *memleak_error1=NULL;"                                           +"\n"+
		            "	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
		            "	free(memleak_error1);"                                               +"\n"+
		            "	memleak_error1[0] = 1;//DEFECT, UFM, memleak_error1"                 +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM"
		            ,
		            },
	/////////////////  7   ///////////////////	
		            {
		            "int* test5(int b){"                                                   +"\n"+
		            "	int *memleak_error1=NULL;"                                           +"\n"+
		            "	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
		            "	if (b > 0) {"                                                        +"\n"+
		            "		free(memleak_error1);"                                              +"\n"+
		            "	}"                                                                   +"\n"+
		            "	int *p;"                                                             +"\n"+
		            "	p = memleak_error1 + 1;//DEFECT, UFM, memleak_error1"                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM"
		            ,
		            },
	/////////////////  8   ///////////////////	
		            {
		            "int* test4(int b){"                                                   +"\n"+
		            "	int *memleak_error1=NULL;"                                           +"\n"+
		            "	memleak_error1=(int*)malloc(sizeof(int)*100);"                       +"\n"+
		            "	if (b > 0) {"                                                        +"\n"+
		            "		free(memleak_error1);"                                              +"\n"+
		            "	}"                                                                   +"\n"+
		            "	memleak_error1[0] = 1;//DEFECT, UFM, memleak_error1"                 +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UFM"
		            ,
		            },
	            
		            
		            
		            
				 
				 
		 });
	 }
}
