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
public class Test_UVF extends ModelTestBase {
	public Test_UVF(String source,String compiletype, String result)
	{
		super(source, compiletype, result);
	}

	@BeforeClass
	public static void setUpBaseChild()
	{
		fsmPath="softtest/rules/gcc/fault/UVF-0.1.xml";
		FSMMachine fsm = FSMLoader.loadXML(fsmPath);
		fsm.setType("fault");
		//每次加入自动机前都清空一下原来的fsms
		FSMAnalysisVisitor.clearFSMS();
		FSMAnalysisVisitor.addFSMS(fsm);

		//加载库函数摘要
		Set<MethodNameDeclaration> libDecls = libManager.compileLib(pre.getLibIncludes());
		interContext = InterContext.getInstance();
		interContext.addLibMethodDecl(libDecls);
	}
	@Parameters
	public static Collection<Object[]> testcaseAndResults()
	{
		return Arrays.asList(new Object[][] {
				//////////////////////////0//////////////////////////////////////////////
				{
					"extern void pfoo(int *p) {return;};"                                  +"\n"+
							"  externintsome_condition(){return 1;};"                              +"\n"+
							"  voiduninit_array_might() {"                                         +"\n"+
							"      int *a[10];"                                                    +"\n"+
							"      if (some_condition()) {"                                        +"\n"+
							"          int i;"                                                     +"\n"+
							"          for(i = 0; i < 10; i++) {"                                  +"\n"+
							"              a[i] = 0;"                                              +"\n"+
							"         }"                                                           +"\n"+
							"     }"                                                               +"\n"+
							"     pfoo(a[4]); //defect"                                            +"\n"+
							"}"                                                                   
							,
							"gcc"
							,
							"OK"
							,
				},
				//////////////////////////1//////////////////////////////////////////////
				{
					"extern void ifoo(int a){};"                                           +"\n"+
							"void uninit_array_must() {"                                           +"\n"+
							"      int a[10];"                                                     +"\n"+
							"      ifoo(a[1]); //defect"                                           +"\n"+
							"}"                                                                  
							,
							"gcc"
							,
							"OK"
							,
				},
				//////////////////////////2//////////////////////////////////////////////
				{//UVF_Exp故障
					"struct s {"                                                           +"\n"+
							"    int a;"                                                           +"\n"+
							"    int b;"                                                           +"\n"+
							"  };"                                                                 +"\n"+
							"  int main() {"                                                       +"\n"+
							"    struct s x;"                                                      +"\n"+
							"    x.b = 0;"                                                         +"\n"+
							"    return x.a; //defect"                                             +"\n"+
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