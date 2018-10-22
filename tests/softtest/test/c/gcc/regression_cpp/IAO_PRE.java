package softtest.test.c.gcc.regression_cpp;

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
				//总用例：23
				//未通过用例：0
				//未通过用例序号:0
				//////////////////////////0//////////////////////////////////////////////
				{
					"void ZX_IAO_FC_1_f1(int i) //记录IAO前置信息"                               +"\n"+
							"{"                                                                    +"\n"+
							"	int b;"                                                              +"\n"+
							"	b = 2/i;"                                                            +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_1_f2(int j) //记录IAO前置信息"                               +"\n"+
							"{"                                                                    +"\n"+
							"	ZX_IAO_FC_1_f1(j);"                                                  +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_1_f3()"                                                +"\n"+
							"{"                                                                    +"\n"+
							"	int b = 2;"                                                          +"\n"+
							"	ZX_IAO_FC_1_f1(b);"                                                  +"\n"+
							"	ZX_IAO_FC_1_f1(0);	//DEFECT, 利用前置信息"                                 +"\n"+
							"	ZX_IAO_FC_1_f2(2);"                                                  +"\n"+
							"	ZX_IAO_FC_1_f2(0); //DEFECT, 利用前置信息"                                 +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"IAO_PRE"
							,
				},
				//////////////////////////1//////////////////////////////////////////////
				{
					"#include<math.h>"                                                     +"\n"+
							""                                                                     +"\n"+
							"int ZX_IAO_FC_2_g1 ;"                                                 +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_2_f1() //记录前置信息"                                       +"\n"+
							"{"                                                                    +"\n"+
							"	int b = 1/ZX_IAO_FC_2_g1; "                                          +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_2_f2()"                                                +"\n"+
							"{"                                                                    +"\n"+
							"	ZX_IAO_FC_2_g1 = 0;"                                                 +"\n"+
							"	ZX_IAO_FC_2_f1();	//DEFECT, 利用前置信息"                                  +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_2_f3(int i, int j) //记录前置信息i != 0"                     +"\n"+
							"{"                                                                    +"\n"+
							"	int b = 1/i; "                                                       +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_2_f4(int j) //记录前置信息j != 0"                            +"\n"+
							"{"                                                                    +"\n"+
							"	ZX_IAO_FC_2_f3(j, 5);"                                               +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_2_f5()"                                                +"\n"+
							"{"                                                                    +"\n"+
							"	int i=0;"                                                            +"\n"+
							"	ZX_IAO_FC_2_f3(i, 4); //DEFECT, IAO"                                 +"\n"+
							"	ZX_IAO_FC_2_f4(i); //DEFECT, IAO"                                    +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"IAO_PRE"
							,
				},
				//////////////////////////2//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_4_f1(int a) //记录IAO函数信息"                               +"\n"+
							"{"                                                                    +"\n"+
							"	div(10, a); "                                                        +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_4_f2()"                                                +"\n"+
							"{"                                                                    +"\n"+
							"	int b = 0;"                                                          +"\n"+
							"	ZX_IAO_FC_4_f1(b); //DEFECT, 利用IAO函数信息"                              +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_4_f3()"                                                +"\n"+
							"{"                                                                    +"\n"+
							"	int b = -2;"                                                         +"\n"+
							"	ZX_IAO_FC_4_f1(b+2); //DEFECT, 利用IAO函数信息,"                           +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"IAO_PRE"
							,
				},

				//////////////////////////3//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"int ZX_IAO_FC_5_global;"                                              +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_5_f1() //记录IAO函数信息[global != 0]"                       +"\n"+
							"{"                                                                    +"\n"+
							"	div(10, ZX_IAO_FC_5_global); "                                       +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_5_f2()"                                                +"\n"+
							"{"                                                                    +"\n"+
							"	ZX_IAO_FC_5_global = 0;"                                             +"\n"+
							"	ZX_IAO_FC_5_f1(); //DEFECT, 利用IAO函数信息"                               +"\n"+
							"}"                                                                     
							,
							"gcc"
							,
							"IAO_PRE"
							,
				},

				//////////////////////////4//////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"int ZX_IAO_FC_6_global;"                                              +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_6_f1(int a) //不单是个变量，是个表达式，记录IAO函数信息[global != 0] "    +"\n"+
							"{"                                                                    +"\n"+
							"	if(a == 0)"                                                          +"\n"+
							"		div(10, ZX_IAO_FC_6_global); "                                      +"\n"+
							"	if(a == 1)"                                                          +"\n"+
							"		div(10, ZX_IAO_FC_6_global+3);"                                     +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_6_f2()"                                                +"\n"+
							"{"                                                                    +"\n"+
							"	ZX_IAO_FC_6_global = 0;"                                             +"\n"+
							"	ZX_IAO_FC_6_f1(0); //DEFECT, 不可做(肖庆)"                                +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"IAO_PRE"
							,
				},

				//////////////////////////5//////////////////////////////////////////////
				{
					"void func1(int i)"                                                    +"\n"+
							"{"                                                                    +"\n"+
							"    int j = i;"                                                       +"\n"+
							"}"                                                                    +"\n"+
							"int func2(int a)"                                                     +"\n"+
							"{"                                                                    +"\n"+
							"    int b = 13;"                                                      +"\n"+
							"    return b/a;       "                                               +"\n"+
							"}"                                                                    +"\n"+
							"void func(int x)"                                                     +"\n"+
							"{"                                                                    +"\n"+
							"    func2(x);"                                                        +"\n"+
							"    if(x != 0)"                                                       +"\n"+
							"        func1(x);                 "                                   +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},

				

				//////////////////////////6//////////////////////////////////////////////
				{
					"int i;"                                                               +"\n"+
							"void f(){"                                                            +"\n"+
							"    int a=1/i;"                                                       +"\n"+
							"}"                                                                    +"\n"+
							"void f1(){"                                                           +"\n"+
							"    f();"                                                             +"\n"+
							"}"                                                                    +"\n"+
							"void f2(){"                                                           +"\n"+
							"    i=0;"                                                             +"\n"+
							"    f1();"                                                            +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"IAO_PRE"
							,
				},

				

				//////////////////////////7//////////////////////////////////////////////
				{//
					"#include <math.h>"                                                    +"\n"+
					""                                                                     +"\n"+
					"int g_val1 = 0;"                                                      +"\n"+
					"int g_val2 = 0;"                                                      +"\n"+
					""                                                                     +"\n"+
					"void func2();"                                                        +"\n"+
					"int func3();"                                                         +"\n"+
					""                                                                     +"\n"+
					"void func1()"                                                         +"\n"+
					"{"                                                                    +"\n"+
					"	func3();"                                                            +"\n"+
					"	func2();"                                                            +"\n"+
					"	func3();"                                                            +"\n"+
					"}"                                                                    +"\n"+
					""                                                                     +"\n"+
					"void func2()"                                                         +"\n"+
					"{"                                                                    +"\n"+
					"	g_val1 = g_val2 = 1;"                                                +"\n"+
					"}"                                                                    +"\n"+
					""                                                                     +"\n"+
					"int func3()"                                                          +"\n"+
					"{"                                                                    +"\n"+
					"	return atan2(g_val1, g_val2); //FP"                              +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"OK"
					,
				},

				
				/////////////////////////8/////////////////////////////////////////////
				//jdh  需要修改  zl
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

				/////////////////////////9/////////////////////////////////////////////
				{
					"void ZX_IAO_FC_1_f1(int i) //记录IAO前置信息"                               +"\n"+
							"{"                                                                    +"\n"+
							"	int b;"                                                              +"\n"+
							"	b = 2/i;"                                                            +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_1_f2(int j) //记录IAO前置信息"                               +"\n"+
							"{"                                                                    +"\n"+
							"	ZX_IAO_FC_1_f1(j);"                                                  +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_1_f3()"                                                +"\n"+
							"{"                                                                    +"\n"+
							"	int b = 2;"                                                          +"\n"+
							"	ZX_IAO_FC_1_f1(b);"                                                  +"\n"+
							"	ZX_IAO_FC_1_f1(0);	//DEFECT, 利用前置信息"                                 +"\n"+
							"	ZX_IAO_FC_1_f2(2);"                                                  +"\n"+
							"	ZX_IAO_FC_1_f2(0); //DEFECT, 利用前置信息"                                 +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"IAO_PRE"
							,
				},
				/////////////////////////10/////////////////////////////////////////////
				{
					"#include<math.h>"                                                     +"\n"+
							""                                                                     +"\n"+
							"int ZX_IAO_FC_2_g1 ;"                                                 +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_2_f1() //记录前置信息"                                       +"\n"+
							"{"                                                                    +"\n"+
							"	int b = 1/ZX_IAO_FC_2_g1; "                                          +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_2_f2()"                                                +"\n"+
							"{"                                                                    +"\n"+
							"	ZX_IAO_FC_2_g1 = 0;"                                                 +"\n"+
							"	ZX_IAO_FC_2_f1();	//DEFECT, 利用前置信息"                                  +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_2_f3(int i, int j) //记录前置信息i != 0"                     +"\n"+
							"{"                                                                    +"\n"+
							"	int b = 1/i; "                                                       +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_2_f4(int j) //记录前置信息j != 0"                            +"\n"+
							"{"                                                                    +"\n"+
							"	ZX_IAO_FC_2_f3(j, 5);"                                               +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_2_f5()"                                                +"\n"+
							"{"                                                                    +"\n"+
							"	int i=0;"                                                            +"\n"+
							"	ZX_IAO_FC_2_f3(i, 4); //DEFECT, IAO"                                 +"\n"+
							"	ZX_IAO_FC_2_f4(i); //DEFECT, IAO"                                    +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"IAO_PRE"
							,
				},
				
				/////////////////////////11/////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_4_f1(int a) //记录IAO函数信息"                               +"\n"+
							"{"                                                                    +"\n"+
							"	div(10, a); "                                                        +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_4_f2()"                                                +"\n"+
							"{"                                                                    +"\n"+
							"	int b = 0;"                                                          +"\n"+
							"	ZX_IAO_FC_4_f1(b); //DEFECT, 利用IAO函数信息"                              +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_4_f3()"                                                +"\n"+
							"{"                                                                    +"\n"+
							"	int b = -2;"                                                         +"\n"+
							"	ZX_IAO_FC_4_f1(b+2); //DEFECT, 利用IAO函数信息,"                           +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"IAO_PRE"
							,
				},

				/////////////////////////12/////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"int ZX_IAO_FC_6_global;"                                              +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_6_f1(int a) //不单是个变量，是个表达式，记录IAO函数信息[global != 0] "    +"\n"+
							"{"                                                                    +"\n"+
							"	if(a == 0)"                                                          +"\n"+
							"		div(10, ZX_IAO_FC_6_global); "                                      +"\n"+
							"	if(a == 1)"                                                          +"\n"+
							"		div(10, ZX_IAO_FC_6_global+3);"                                     +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_6_f2()"                                                +"\n"+
							"{"                                                                    +"\n"+
							"	ZX_IAO_FC_6_global = 0;"                                             +"\n"+
							"	ZX_IAO_FC_6_f1(0); //DEFECT, 不可做(肖庆)"                                +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"IAO_PRE"
							,
				},
				/////////////////////////13/////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"int ZX_IAO_FC_6_global;"                                              +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_6_f1(int a) //不单是个变量，是个表达式，记录IAO函数信息[global != 0] "    +"\n"+
							"{"                                                                    +"\n"+
							"	if(a == 0)"                                                          +"\n"+
							"		div(10, ZX_IAO_FC_6_global); "                                      +"\n"+
							"	if(a == 1)"                                                          +"\n"+
							"		div(10, ZX_IAO_FC_6_global+3);"                                     +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_6_f2()"                                                +"\n"+
							"{"                                                                    +"\n"+
							"	ZX_IAO_FC_6_global = 0;"                                             +"\n"+
							"	ZX_IAO_FC_6_f1(0); //DEFECT, 不可做(肖庆)"                                +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"IAO_PRE"
							,
				},
				/////////////////////////14/////////////////////////////////////////////
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
				////////////////////////15////////////////////////////////////////////
				{
					//函数间计算时，参数相关的区间运算无法精确
					//noted by zhouhb
					//jdh  暂不处理
					"int jhb_iao_3_f1(int b){"                                             +"\n"+
					"	return 2*b;"                                                         +"\n"+
					"}"                                                                    +"\n"+
					"int jhb_iao_3_f2(int t,int m){"                                       +"\n"+
					"		int x=jhb_iao_3_f1(m);"                                             +"\n"+
					"		return (x/(t-x));"                                                  +"\n"+
					"}"                                                                    +"\n"+
					"void jhb_iao_3_f1(){"                                                 +"\n"+
					"		int i;"                                                             +"\n"+
					"		i=jhb_iao_3_f2(10,5);  //DEFECT"                                    +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"OK"
					,
				},
				/////////////////////////16/////////////////////////////////////////////
				{
					//当函数参数和全局变量相关时，其约束条件计算会存在问题
					//jdh  暂不处理
					"int t=5;"                                                            +"\n"+
					"int jhb_iao_3_f2(int x){"                                             +"\n"+
					"		"                                                                   +"\n"+
					"		return (x/(t-x));"                                                  +"\n"+
					"}"                                                                    +"\n"+
					"void jhb_iao_3_f1(){"                                                 +"\n"+
					"		int i;"                                                             +"\n"+
					"		i=jhb_iao_3_f2(5);  //DEFECT"                                       +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"OK"
					,
				},
				/////////////////////////17/////////////////////////////////////////////
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
							"gcc","IAO_PRE"
							,
				},
				
				
				
				/////////////////////////18/////////////////////////////////////////////
				{
					"void ZX_IAO_FC_1_f1(int i) //记录IAO前置信息"                               +"\n"+
							"{"                                                                    +"\n"+
							"	int b;"                                                              +"\n"+
							"	b = 2/i;"                                                            +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_1_f2(int j) //记录IAO前置信息"                               +"\n"+
							"{"                                                                    +"\n"+
							"	ZX_IAO_FC_1_f1(j);"                                                  +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_1_f3()"                                                +"\n"+
							"{"                                                                    +"\n"+
							"	int b = 2;"                                                          +"\n"+
							"	ZX_IAO_FC_1_f1(b);"                                                  +"\n"+
							"	ZX_IAO_FC_1_f1(0);	//DEFECT, 利用前置信息"                                 +"\n"+
							"	ZX_IAO_FC_1_f2(2);"                                                  +"\n"+
							"	ZX_IAO_FC_1_f2(0); //DEFECT, 利用前置信息"                                 +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"IAO_PRE"
							,
				},
				/////////////////////////19/////////////////////////////////////////////
				{
					"#include<math.h>"                                                     +"\n"+
							""                                                                     +"\n"+
							"int ZX_IAO_FC_2_g1 ;"                                                 +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_2_f1() //记录前置信息"                                       +"\n"+
							"{"                                                                    +"\n"+
							"	int b = 1/ZX_IAO_FC_2_g1; "                                          +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_2_f2()"                                                +"\n"+
							"{"                                                                    +"\n"+
							"	ZX_IAO_FC_2_g1 = 0;"                                                 +"\n"+
							"	ZX_IAO_FC_2_f1();	//DEFECT, 利用前置信息"                                  +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_2_f3(int i, int j) //记录前置信息i != 0"                     +"\n"+
							"{"                                                                    +"\n"+
							"	int b = 1/i; "                                                       +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_2_f4(int j) //记录前置信息j != 0"                            +"\n"+
							"{"                                                                    +"\n"+
							"	ZX_IAO_FC_2_f3(j, 5);"                                               +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_2_f5()"                                                +"\n"+
							"{"                                                                    +"\n"+
							"	int i=0;"                                                            +"\n"+
							"	ZX_IAO_FC_2_f3(i, 4); //DEFECT, IAO"                                 +"\n"+
							"	ZX_IAO_FC_2_f4(i); //DEFECT, IAO"                                    +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"IAO_PRE"
							,
				},
				

				////////////////////////20/////////////////////////////////////////////
				{
					"#include <stdlib.h>"                                                  +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_4_f1(int a) //记录IAO函数信息"                               +"\n"+
							"{"                                                                    +"\n"+
							"	div(10, a); "                                                        +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_4_f2()"                                                +"\n"+
							"{"                                                                    +"\n"+
							"	int b = 0;"                                                          +"\n"+
							"	ZX_IAO_FC_4_f1(b); //DEFECT, 利用IAO函数信息"                              +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_4_f3()"                                                +"\n"+
							"{"                                                                    +"\n"+
							"	int b = -2;"                                                         +"\n"+
							"	ZX_IAO_FC_4_f1(b+2); //DEFECT, 利用IAO函数信息,"                           +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"IAO_PRE"
							,
				},
				//////////////////////////////////////////////21/////////////////////////////////////////////
				{
					"int aa(){"                                                            +"\n"+
							"	return 0;"                                                           +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int ff(int b){"                                                           +"\n"+
							"	  int c;"                                                              +"\n"+
							"    c=1/b;"                                                           +"\n"+
							"    return c;"                                                        +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void hh(){"                                                           +"\n"+
							"	 int h;"                                                     +"\n"+
							"	 h=ff(aa());"                                                     +"\n"+
							"} "                                                                   
							,
							"gcc"
							,
							"IAO_PRE"
							,
				},
				//////////////////////////////////////22/////////////////////////////////////////////////////
				//jdh  需要修改  zl
				//zl,20111102，zl，已修改
				{
					"struct aa{"                                                           +"\n"+
							"int x;"                                                             +"\n"+
							"};"                                                                   +"\n"+
							""                                                                     +"\n"+
							"int ff(int b){"                                                       +"\n"+
							"	int c;"                                                              +"\n"+
							"    c=1/b;"                                                           +"\n"+
							"    return c;"                                                        +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void hh(){"                                                           +"\n"+
							"	int h;"                                                              +"\n"+
							"    struct aa y; y.x=0;"                                                            +"\n"+
							"    h=ff(y.x); "                                                      +"\n"+
							"} "                                                                   
							,
							"gcc"
							,
							"IAO_PRE"
							,
				},


		});
	}
}
