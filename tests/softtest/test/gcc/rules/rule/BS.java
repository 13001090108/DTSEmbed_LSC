package softtest.test.gcc.rules.rule;

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
public class BS extends ModelTestBase {
	public BS(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/rule/BS-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("rule");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);
	}
	
	 @Parameters
	 public static Collection<Object[]> testcaseAndResults()
	 {
		 return Arrays.asList(new Object[][] {
	
	/////////////////  0   ///////////////////	
		            {
		            "void f(){"                                                            +"\n"+
		            "int a=1;"                                                             +"\n"+
		            "switch(a);}"                                                         
		            ,
		            "gcc"
		            ,
		            "BS"
		            ,
		            },
	/////////////////  1   ///////////////////	
		            {
		            "void f(){"                                                            +"\n"+
		            "int a=1;"                                                             +"\n"+
		            "switch(a){}}"                                                          
		            ,
		            "gcc"
		            ,
		            "BS"
		            ,
		            },
	/////////////////  2   ///////////////////	
		            {
		            "void f(){"                                                            +"\n"+
		            "int a=1;"                                                             +"\n"+
		            "switch(a){;;;;;;}}"                                                          
		            ,
		            "gcc"
		            ,
		            "BS"
		            ,
		            },
	/////////////////  3   ///////////////////	
		            {
		            "void f(){"                                                            +"\n"+
		            "int a=1;"                                                             +"\n"+
		            "switch(a){"                                                           +"\n"+
		            "case 0:printf(\"yes\");"                                                +"\n"+
		            "case 1:printf(\"no\");}"                                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  4   ///////////////////	
		            {
		            "void f(){"                                                            +"\n"+
		            "int a=1;"                                                             +"\n"+
		            "switch(a){"                                                           +"\n"+
		            "case 1:a=1;break;"                                                    +"\n"+
		            "case 2:a=2;break;"                                                    +"\n"+
		            "default:break;"                                                       +"\n"+
		            "}}"                                                                   
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },




 
		           
		 });
		 
		 
	 }
}
