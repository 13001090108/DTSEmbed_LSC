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
/**zys	2011.6.24
 * 本测试用例在单独回归时，一切正常；其他回归测试用例也有类似情况
 * 如果跟其他测试用例（OOB_PRE）同时运行，则出现OOB_PRE中的空指针异常；
 * 
 * 原因是测试用例中的库函数并没有相应头文件中的函数原型，在获取函数声明时失败导致的。
 * 
 * 可以参考其他回归测试的框架，并改写测试用例使之能编译通过。
 * */
@RunWith(Parameterized.class)
public class UVF extends ModelTestBase{
	public UVF(String source,String compiletype, String result)
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
		LIB_SUMMARYS_PATH="gcc_lib/bo_summary.xml";
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
		            "void func4()"                                                         +"\n"+
		            "{	"                                                                   +"\n"+
		            "	int b;"                                                              +"\n"+
		            "	int a;"                                                              +"\n"+
		            "	b = a;  //DEFECT,UVF,a"                                              +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UVF"
		            ,
		            },
			 
	/////////////////  2   ///////////////////	
		            {
		            "typedef struct {"                                                     +"\n"+
		            "	int i;"                                                              +"\n"+
		            "	int j;"                                                              +"\n"+
		            "}Test;"                                                               +"\n"+
		            "void test1(){"                                                        +"\n"+
		            "	Test a,b;"                                                           +"\n"+
		            "	b.i=a.j;//DEFECT, UVF, a"                                            +"\n"+
		            "	a.i=b.j; "                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UVF"
		            ,
		            },
			 
	/////////////////  3   ///////////////////	
		            {
		            "int  f(int i)  {return i;}"                                           +"\n"+
		            "void  fun(int i, int j) {  }"                                         +"\n"+
		            "int main(int argc, char* argv[ ])"                                    +"\n"+
		            "{   "                                                                 +"\n"+
		            "	int k,m;"                                                            +"\n"+
		            "	int i;	 "                                                            +"\n"+
		            "	int b = f(i);"                                                       +"\n"+
		            "	fun(k,m);"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UVF"
		            ,
		            },

		            
	/////////////////  4   ///////////////////	
		            {
		            "int fun (int i)"                                                      +"\n"+
		            "{"                                                                    +"\n"+
		            "	return i;"                                                           +"\n"+
		            "}"                                                                    +"\n"+
		            "int test () {"                                                        +"\n"+
		            "	int i ;"                                                             +"\n"+
		            "	int j = fun ( i);  //DEFECT,UVF,i"                                   +"\n"+
		            "	i = fun(2);"                                                         +"\n"+
		            "	j = i;"                                                              +"\n"+
		            "	return 0;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UVF"
		            ,
		            },
	/////////////////  5   ///////////////////	
		            {
		            "void test1(int i) "                                                   +"\n"+
		            "{"                                                                    +"\n"+
		            "	int *c;"                                                             +"\n"+
		            "	switch(i){"                                                          +"\n"+
		            "		case 1:"                                                            +"\n"+
		            "		default:"                                                           +"\n"+
		            "			c=&i;"                                                             +"\n"+
		            "			break;"                                                            +"\n"+
		            "		case 2:"                                                            +"\n"+
		            "			c=&i;"                                                             +"\n"+
		            "			break;"                                                            +"\n"+
		            "		case 3:"                                                            +"\n"+
		            "			break;"                                                            +"\n"+
		            "	}"                                                                   +"\n"+
		            "	c++;   //DEFECT,UVF,c"                                               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UVF"
		            ,
		            },
	/////////////////  6   ///////////////////	
		            {
		            "void test3(int i){"                                                   +"\n"+
		            "	int value;"                                                          +"\n"+
		            "	if(i==1)"                                                            +"\n"+
		            "		value=1;"                                                           +"\n"+
		            "	if(i==2)"                                                            +"\n"+
		            "		value=2;"                                                           +"\n"+
		            "	if(i==3)"                                                            +"\n"+
		            "		value=3;"                                                           +"\n"+
		            "	if(i<4)"                                                             +"\n"+
		            "		value++;  //DEFECT, UVF, value"                                     +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UVF"
		            ,
		            },

				 
		 });
	 }
}


