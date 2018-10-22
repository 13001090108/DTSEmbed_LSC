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
/**zys	2011.6.24
 * 本测试用例在单独回归时，一切正常；其他回归测试用例也有类似情况
 * 如果跟其他测试用例（OOB_PRE）同时运行，则出现OOB_PRE中的空指针异常；
 * 
 * 原因是测试用例中的库函数并没有相应头文件中的函数原型，在获取函数声明时失败导致的。
 * 
 * 可以参考其他回归测试的框架，并改写测试用例使之能编译通过。
 * */
@RunWith(Parameterized.class)
public class Test_UVF extends ModelTestBase{
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
////////////////	/  0   ///////////////////	
				{
		            "void call(int);"                                                      +"\n"+
		            ""                                                                     +"\n"+
		            "void f1()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	int i;"                                                              +"\n"+
		           // "	int j = 2;"                                                          +"\n"+
		            "	call(i);  //DEFECT, UVF, i"                                          +"\n"+
		           // "	call(j); //FP "                                                      +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UVF"
		            ,
		            },
	
////////////////	/  1   chh///////////////////	
		             {
		            "void f3()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	int j;"                                                              +"\n"+
		            "	int m;"                                                              +"\n"+
		            "	m += 1; //DEFECT, UVF, m"                                            +"\n"+
		            "	j++; //DEFECT, UVF, j"                                               +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UVF"
		            ,
		            },
////////////////	/  2   chh///////////////////	
		            {
		            "void f4() {"                                                          +"\n"+
		            "  int k;"                                                             +"\n"+
		            "  int a = 2;"                                                         +"\n"+
		            "  a = k;   //DEFECT, UVF, k"                                          +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UVF"
		            ,
		            },
////////////////	/  3  chh ///////////////////	
		            {
		            "void f5()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	int a;"                                                              +"\n"+
		            "	int b;"                                                              +"\n"+
		            "	b = a; //DEFECT, UVF, a"                                             +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UVF"
		            ,
		            },
////////////////	/  4  chh   普通函数初始化///////////////////	
		             {
		            "int getValue(int);"                                                   +"\n"+
		            ""                                                                     +"\n"+
		            "int f7()"                                                             +"\n"+
		            "{"                                                                    +"\n"+
		            "    int	c;"                                                           +"\n"+
		            "    return (c = getValue(0)) == 1 ? 1 : getValue(c); //FP"            +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
////////////////	/  5   chh  input(int*)函数初始化///////////////////	
		            {
		            "void input(int*);"                                                    +"\n"+
		            ""                                                                     +"\n"+
		            "int f10()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	int ii;"                                                             +"\n"+
		            "	input(&ii); //FP"                                                    +"\n"+
		            "	return ii;"                                                           +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  6   chh  sscanf函数初始化///////////////////---------------		
		            {
		            "void fun()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "	char c[],d[];"                                                         +"\n"+
		                                                               
		            "	sscanf(\"123456\",\"%s\",c);//FP"                                            +"\n"+
		            "	d=c;;"                                                        +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            
		            "OK"
		            ,
		            },
	/////////////////  7  chh strcpy初始化 ///////////////////---------------	
		             {
		            "void fun()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "char st1[],st2[]=\"aaaaa\";"                                                  +"\n"+
		            "strcpy(st1,st2);"                                                    +"\n"+
		            "}" 
		            ,
		            "gcc"
		            ,
		            
		            "OK"
		            ,
		            },
/////////////////  8  chh strcpy初始化不合法 ///////////////////---------------	
		             {
		            "void fun()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "char st1[];"                                                  +"\n"+
		            "strcpy(st1,st1);"                                                    +"\n"+
		            "}" 
		            ,
		            "gcc"
		            ,
		            
		            "UVF"
		            ,
		            },
	/////////////////  9  chh strcpy初始化不合法 ///////////////////--------------	
				  {
		            "void fun()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "char str2[],str1[];"                                                  +"\n"+
		            "strcpy(str1,str2);"                                                    +"\n"+
		            "}" 
		            ,
		            "gcc"
		            ,
		            
		            "UVF"
		            ,
		            },
/////////////////  10   chh  f(int *i)函数初始化///////////////////	
		             {
		            "void f(int *i);"                                                 +"\n"+
		            "void fun()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "	int a[],c[];"                                                    +"\n"+
		            "	f(a);"                                                    +"\n"+
		            "	c=a;"                                                             +"\n"+
		            "}" 
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },

	/////////////////  11  chh  i=i+1///////////////////	
		            {
		            "fun()"                                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "	int i;"                                                         +"\n"+
		            "	i=i+1;//DEFECT, UVF, i"                                                              +"\n"+
		            "}"
		            ,
		            "gcc"
		            ,
		            "UVF"
		            ,
		            },
/////////////////  12 chh for 内先使用后初始化   ///////////////////	
		            {
		            "f()"                                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "char a;"                                                              +"\n"+
		            "for(;;){a++;a=0;}"                                                      +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UVF"
		            ,
		            },
	/////////////////  13 chh if 内先使用后初始化   ///////////////////	
		            {
		            "f()"                                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "char a;"                                                              +"\n"+
		            "if(1){a++;a=0;}"                                                      +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UVF"
		            ,
		            },		            
/////////////////  14   chh 数组初始化不合法///////////////////----------------	
		    		
		            {
		            "fun()"                                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "	int a[];"                                                        +"\n"+
		            "	a[0]=a[1];"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UVF"
		            ,
		            },
/////////////////  15   chh  数组初始化///////////////////----------------	
		    		
		            {
		            "fun()"                                                                +"\n"+
		            "{"                                                                    +"\n"+
		            "	int a[];"                                                        +"\n"+
		            "	a[0]=a[1]=0;"                                                                +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "OK"
		            ,
		            },
	/////////////////  16   chh sizeof(i)不算对i的非法使用///////////////////	
		              {
		            "int fun()"                                                            +"\n"+
		            "{"                                                                    +"\n"+
		            "	int i;"                                                              +"\n"+
		            "	"                                                                    +"\n"+
		            "	return sizeof(i);"                                                   +"\n"+
		            "}"  
		            ,
		            "gcc"		           
		            ,
		            "OK"
		            ,
		            },

/////////////////  17  chh strcpy初始化 ///////////////////-----------	
		            {
		            "void fun()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "char st1[],st2[];"                                                  +"\n"+
		            "strcmp(st1,st2);"                                                    +"\n"+
		            "}" 
		            ,
		            "gcc"
		            ,
		            
		            "UVF"
		            ,
		            },
	/////////////////  18 ///////////////////	
		             {
		            "void fun()"                                                           +"\n"+
		            "{"                                                                    +"\n"+
		            "int i;"                                                  +"\n"+
		            "i&=0x03;"                                                    +"\n"+
		            "}" 
		            ,
		            "gcc"
		            ,
		            
		            "OK"
		            ,
		            },         
/////////////////  19  chh  for_out///////////////////	//
				     {
			            " fun()"                                                            +"\n"+
			            "{"                                                                    +"\n"+
			            "	int i,k;"                                                              +"\n"+
			            "	for(i=0;i>5;i++)"                                                    +"\n"+
			            "	{"                                                                   +"\n"+
			            "		//k=i;"                                                             +"\n"+
			            "	}"                                                                   +"\n"+
			            "	k=5;"                                                           +"\n"+
			            "}"                                                                    
			            ,
			            "gcc"		           
			            ,
			            "OK"
			            ,
			            }, 
/////////////////  20  chh while_head///////////////////	
			             {
			            "void  f()"                                                            +"\n"+
			            "{"                                                                    +"\n"+
			            "int a,b=0;"                                                             +"\n"+
			            "while(b<5)"                                                           +"\n"+
			            "{"                                                                    +"\n"+
			            "b++;"                                                                 +"\n"+
			            "}"                                                                    +"\n"+
			            "a=b;}"                                                                    
			            ,
			            "gcc"
			            ,
			            "OK"
			            ,
			            },
/////////////////  21  chh   do_while_head///////////////////	
						  {
					            ""                                                                     +"\n"+
					            "void fun()"                                                            +"\n"+
					            "{"                                                                    +"\n"+
					            "	int i,k;"                                                          +"\n"+
					            "	k=0;"                                                          +"\n"+
					            "	do{"                                                                 +"\n"+
					            "	    i=k;"                                                                 +"\n"+
					            "		"                                                               +"\n"+
					            "		k++;"                                                               +"\n"+
					            "		}while(i<10);"                                                       +"\n"+
					            "		i++;"                                                               +"\n"+
					            "}"
					            ,
					            "gcc"
					            ,
					            "OK"
					            ,
					            },
		

/////////////////  22   chh   for不可达初始化///////////////////	////
			            {
				            
				            "int fun()"                                                            +"\n"+
				            "{"                                                                    +"\n"+
				            "	int i,k,j;"                                                            +"\n"+
				            "	for(i=12;i<10;i++)//条件不符合，不会进入for循环，k没有初始化，但是结果OK"                                                    +"\n"+
				            "	{"                                                                   +"\n"+
				            "		//break;"                                                                   +"\n"+
				            "		k=i;"                                                                   +"\n"+
				            "	}"                                                               +"\n"+
				            "	j=k;"                                                                   +"\n"+
				            "}"
				            ,
				            "gcc"
				            ,
				            "UVF"
				            ,
				            },

/////////////////  23  chh if 不可达初始化///////////////////	
				             {
				            "void fun()"                                                           +"\n"+
				            "{"                                                                    +"\n"+
				            "	int i=1,x,n;"                                                        +"\n"+
				            "	if(i==0) scanf(\"%d\",&x);//判断条件不成立，即x未赋值，依旧OK"                                            +"\n"+
				            "	n=x;"                                                                +"\n"+
				            "}" 
				            ,
				            "gcc"
				            ,
				            
				            "UVF"
				            ,
				            },
/////////////////  24 chh switch初始化不可达   ///////////////////	
				            {
				            "void fun()"                                                           +"\n"+
				            "{"                                                                    +"\n"+
				            "int i,a,b;"                                                         +"\n"+
				            "i=0;"                                                                   +"\n"+
				            "switch(i)"                                                            +"\n"+
				            "{"                                                                    +"\n"+
				            "case 1:a=2;break;"                                                    +"\n"+
				            "default:break;"                                                       +"\n"+
				            "}"                                                                    +"\n"+
				            "b=a;"                                                                 +"\n"+
				            "}"                                                                    
				            ,
				            "gcc"
				            ,
				            "UVF"
				            ,
				            },
/////////////////  25 chh  if初始化不可达  ///////////////////	
	
						             {
						            "void  f()"                                                            +"\n"+
						            "{"                                                                    +"\n"+
						            "int j,y,x;"                                                             +"\n"+
						            "x=1;"                                                                 +"\n"+
						            "y=x+1;"                                                               +"\n"+
						            "if(x>y)"                                                              +"\n"+
						            "{"                                                                    +"\n"+
						            "j=5;"                                                                 +"\n"+
						            "}"                                                                    +"\n"+
						            "x=j;"                                                                 +"\n"+
						            "}"                                                                    
						            ,
						            "gcc"
						            ,
						            "UVF"
						            ,
						            },
	
/////////////////  26 chh do_while 内先使用后初始化   ///////////////////	
		            {
		            "f()"                                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "char a;"                                                              +"\n"+
		            "do{a++;a=0;}while(1);"                                                      +"\n"+
		            "}"                                                                    
		            ,
		            "gcc"
		            ,
		            "UVF"
		            ,
		            },
	/////////////////  27 chh while 内先使用后初始化   ///////////////////	
		            {
		            "f()"                                                                  +"\n"+
		            "{"                                                                    +"\n"+
		            "char a;"                                                              +"\n"+
		            "while(1){a++;a=0;}"                                                      +"\n"+
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


