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
public class Test_IAO extends ModelTestBase{
	public Test_IAO(String source,String compiletype, String result)
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
		            "f(){"                                                                 +"\n"+
		            "	int i,j;"                                                            +"\n"+
		            "	i=0;"                                                                +"\n"+
		            "	j/=i;"                                                               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "IAO"
		            ,
		            },
	/////////////////  1   ///////////////////	
		            {
		            "f(){"                                                                 +"\n"+
		            "	int i,j;"                                                            +"\n"+
		            "	i=0;"                                                                +"\n"+
		            "	j=j/i;"                                                               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "IAO"
		            ,
		            },			 
	/////////////////  2   ///////////////////	
		            {
		            "f(){"                                                                 +"\n"+
		            "	int i,j;"                                                            +"\n"+
		            "	i=j;"                                                                +"\n"+
		            "	j/=i-j;"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "IAO"
		            ,
		            },
	/////////////////  3   ///////////////////	
		            {
		            "f(){"                                                                 +"\n"+
		            "	int i,j;"                                                            +"\n"+
		            "	i=j;"                                                                +"\n"+
		            "	j=j/(i-j);"                                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "IAO"
		            ,
		            },
		        	/////////////////  4   ///////////////////	
		            {
		            "f(){"                                                                 +"\n"+
		            "	int i,j;"                                                            +"\n"+
		            "	i=j;"                                                                +"\n"+
		            "	j=j/(i-j+1);"                                                             +"\n"+
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
