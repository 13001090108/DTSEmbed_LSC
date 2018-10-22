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
				//总用例：36
				//未通过用例：2
				//未通过用例序号:23,27
				//////////////////////////0//////////////////////////////////////////////
				{
					"int func3()"                                                          +"\n"+
							"{"                                                                    +"\n"+
							"    int a = 0, b = 10;"                                               +"\n"+
							"    b /= a; // DEFECT, IAO, "                                         +"\n"+
							"    return 0;"                                                        +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"IAO"
							,
				},
				
				//////////////////////////1//////////////////////////////////////////////
				{
					"#include<stdlib.h>"                                                   +"\n"+
							""                                                                     +"\n"+
							"int func1()"                                                          +"\n"+
							"{"                                                                    +"\n"+
							"	int a = 0;"                                                          +"\n"+
							"	div(10, a); // DEFECT, IAO, "                                        +"\n"+
							"	return 0;"                                                           +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"IAO"
							,
				},
				//////////////////////////2//////////////////////////////////////////////
				{
					"#include<stdlib.h>"                                                   +"\n"+
							""                                                                     +"\n"+
							"int func2()"                                                          +"\n"+
							"{"                                                                    +"\n"+
							"	int a = 0;"                                                          +"\n"+
							"	ldiv(10, a); // DEFECT, IAO, "                                       +"\n"+
							"	return 0;"                                                           +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"IAO"
							,
				},
				//////////////////////////3////////////////////////////////////////	
				{
					"int b = 0;"                                                           +"\n"+
							"int func8()"                                                          +"\n"+
							"{"                                                                    +"\n"+
							"	int a = 10, b = 0;"                                                  +"\n"+
							"	a = a / b + 100; // DEFECT, IAO, "                                   +"\n"+
							"	return 0;"                                                           +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int func9()"                                                          +"\n"+
							"{"                                                                    +"\n"+
							"	1/b; //FP"                                                           +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"IAO"
							,
				},
				//////////////////////////4//////////////////////////////////////////////
				{
					"#include<math.h>"                                                     +"\n"+
							""                                                                     +"\n"+
							"int func3()"                                                          +"\n"+
							"{"                                                                    +"\n"+
							"	double a = -1.0;"                                                    +"\n"+
							"	double b = log(a); // DEFECT, IAO, "                                 +"\n"+
							"	return 0;"                                                           +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"IAO"
							,
				},
				//////////////////////////5//////////////////////////////////////////////
				{
					"void ghx_iao_1_f1()"                                                  +"\n"+
							"{"                                                                    +"\n"+
							"int i;"                                                               +"\n"+
							"int n=1;"                                                             +"\n"+
							"int nn=0;"                                                            +"\n"+
							"int mm=0;"                                                            +"\n"+
							"for(i=0;i<n;i++)"                                                     +"\n"+
							"{"                                                                    +"\n"+
							"++nn;"                                                                +"\n"+
							"}"                                                                    +"\n"+
							"mm/=nn;//FP"                                                          +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				//////////////////////////6//////////////////////////////////////////////	
				{//全局函数副作用，在函数中认为全局函数的区间未知
					"int global = 0;"                                                    +"\n"+
							""                                                                     +"\n"+
							"int func1() {"                                                        +"\n"+
							" 	int t;"                                                             +"\n"+
							" 	t = 1 / global; // FP, IAO, "                                   +"\n"+
							" 	t = 1 / func(); "                                   +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void func()"                                                          +"\n"+
							"{"                                                                    +"\n"+
							"    double sqrt(doublet);//FP, IAO"                                   +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				//////////////////////////7//////////////////////////////////////////////
				{
					"#include <assert.h>"                                                  +"\n"+
							"void ghx_iao_2_f2()"                                                  +"\n"+
							"{"                                                                    +"\n"+
							"int p;"                                                               +"\n"+
							"int f;"                                                               +"\n"+
							"assert(f>0);"                                                         +"\n"+
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
				//////////////////////////8//////////////////////////////////////////////
				{
					"#include \"math.h\""                                                    +"\n"+
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
				//////////////////////////9//////////////////////////////////////////////
				{
					"#include \"math.h\""                                                    +"\n"+
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
				//////////////////////////10//////////////////////////////////////////////
				{
					"#include \"math.h\""                                                    +"\n"+
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
				//////////////////////////11//////////////////////////////////////////////
				{
					"#include \"math.h\""                                                    +"\n"+
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
				//////////////////////////12//////////////////////////////////////////////
				{
					"void jhb_iao_1_f1(){"                                                 +"\n"+
							"  int a=0;"                                                           +"\n"+
							"  int* p=&a;"                                                         +"\n"+
							"  a=a/(*p);"                                                          +"\n"+
							"   "                                                                  +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				//////////////////////////13//////////////////////////////////////////////
				{
					""                                                                     +"\n"+
							"int global = 0;"                                                      +"\n"+
							"int func() {"                                                         +"\n"+
							"	return 0;"                                                           +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"int gfunc(int b) {"                                                   +"\n"+
							"	int a = 0;"                                                          +"\n"+
							"	return b/a; // DEFECT, IAO, "                                        +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"IAO"
							,
				},

				//////////////////////////14//////////////////////////////////////////////
				//区间无法精确到真分支上a大于0，导致误报，无法修改
				//noted by zhouhb
				//可以保留该错误  jdh
				{
					"void f(int a, int b)"                                                 +"\n"+
							"{"                                                                    +"\n"+
							"     int y;"                                                          +"\n"+
							"     if (a >= 0)"                                                     +"\n"+
							"     {"                                                               +"\n"+
							"          if (((a * 255 + b) >= 0) && (b < 255))"                     +"\n"+
							"          {"                                                          +"\n"+
							"    	      if ((a * 255 + b) > 255)"                                  +"\n"+
							"			      y = (int) ((255- b)/a + 0.5);  //FP"                         +"\n"+
							"          }    "                                                      +"\n"+
							"     }     "                                                          +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"IAO"
							,
				},

				//////////////////////////15//////////////////////////////////////////////
				//区间无法精确到真分支上a大于0，导致误报，无法修改
				//noted by zhouhb
				//可以保留该错误  jdh
				{
					"void f(int a, int b)"                                                 +"\n"+
							"{"                                                                    +"\n"+
							"     int x;"                                                          +"\n"+
							"     if (a >= 0)"                                                     +"\n"+
							"     {"                                                               +"\n"+
							"          if (((a * 255 + b) >= 0) && (b < 255))"                     +"\n"+
							"          {"                                                          +"\n"+
							"              if (b < 0)"                                             +"\n"+
							"                  x = (int) (- b/a + 0.5);  //FP"                     +"\n"+
							"          }    "                                                      +"\n"+
							"     }     "                                                          +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"IAO"
							,
				},

				//////////////////////////16//////////////////////////////////////////////
				{
					"void ghx_iao_1_f1()"                                                  +"\n"+
							"{"                                                                    +"\n"+
							"int i;"                                                               +"\n"+
							"int n=1;"                                                             +"\n"+
							"int nn=0;"                                                            +"\n"+
							"int mm=0;"                                                            +"\n"+
							"for(i=0;i<n;i++)"                                                     +"\n"+
							"{"                                                                    +"\n"+
							"++nn;"                                                                +"\n"+
							"}"                                                                    +"\n"+
							"mm/=nn;//FP"                                                          +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},

				//////////////////////////17/////////////////////////////////////////////
				{
					"#include \"math.h\""                                                    +"\n"+
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

				//////////////////////////18//////////////////////////////////////////////
				{
					"#include <assert.h>"                                                  +"\n"+
							"void ghx_iao_2_f2()"                                                  +"\n"+
							"{"                                                                    +"\n"+
							"int p;"                                                               +"\n"+
							"int f;"                                                               +"\n"+
							"assert(f>0);"                                                         +"\n"+
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

				//////////////////////////19//////////////////////////////////////////////
				{
					"#include \"math.h\""                                                    +"\n"+
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

				//////////////////////////20//////////////////////////////////////////////
				{
					"#include \"math.h\""                                                    +"\n"+
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

				//////////////////////////21//////////////////////////////////////////////
				{
					"#include \"math.h\""                                                    +"\n"+
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

				//////////////////////////22//////////////////////////////////////////////
				{
					"#include <string.h>"                                                  +"\n"+
							"#include <stdio.h>"                                                   +"\n"+
							""                                                                     +"\n"+
							"#define  s 2.3333"                                                    +"\n"+
							""                                                                     +"\n"+
							"main(){"                                                              +"\n"+
							"	int i=2/s;"                                                          +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},

				/////////////////////////23/////////////////////////////////////////////
				//区间问题，可修改
				//noted by zhouhb
				//jdh  需要修改  zhb
				{
					"#include <math.h>"                                                    +"\n"+
							"void f()"                                                             +"\n"+
							"{"                                                                    +"\n"+
							"    static double c = -0.095;"                                        +"\n"+
							"    double sq = sqrt(1.0 + c * c);"                                   +"\n"+
							"    double a = 1.0 / sq;"                                             +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},

				
				/////////////////////////24/////////////////////////////////////////////
				{
					//区间问题，可修改
					//noted by zhouhb
					//jdh  需要修改  zhb

					"void f(unsigned int i)"                                               +"\n"+
					"{"                                                                    +"\n"+
					"    if (i != 0 && i <= 8)"                                            +"\n"+
					"        int j = ((32 / i) + 5) / (32 / i);    "                       +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"OK"
					,
				},

				/////////////////////////25/////////////////////////////////////////////
				{
					""                                                                     +"\n"+
							""                                                                     +"\n"+
							"int func(int var)"                                                    +"\n"+
							"{"                                                                    +"\n"+
							"	if (var != -1)"                                                      +"\n"+
							"		return var != 0 ? 1 / var : 0; //FP"                                +"\n"+
							""                                                                     +"\n"+
							"	return 0;"                                                           +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},

				/////////////////////////26/////////////////////////////////////////////
				{
					//指针的值关联问题，精度有待提高，暂时不支持
					//noted by zhouhb
					//可以保留该错误 jdh
					//zl,与测试用例12相同
					"void jhb_iao_1_f1(){"                                                 +"\n"+
					"  int a=0;"                                                           +"\n"+
					"  int* p=&a;"                                                         +"\n"+
					"  a=a/(*p);   //DEFECT"                                               +"\n"+
					"   "                                                                  +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"OK"
					,
				},



				/////////////////////////27/////////////////////////////////////////////
				//经过两条赋值语句后AbsSinus的值限定在-1和1之间，不应该报出
				//noted by zhouhb
				{
					"#include \"math.h\""                                                    +"\n"+
							""                                                                     +"\n"+
							"double f_IAO_1(double AbsSinus,double cosinus)"                       +"\n"+
							"{"                                                                    +"\n"+
							"	AbsSinus = (AbsSinus > 1) ? 1 : AbsSinus;"                           +"\n"+
							"	AbsSinus = (AbsSinus < -1) ? -1 : AbsSinus;"                         +"\n"+
							""                                                                     +"\n"+
							"	if(AbsSinus > 1)"                                                    +"\n"+
							"	{"                                                                   +"\n"+
							"		//..."                                                              +"\n"+
							"	}"                                                                   +"\n"+
							"	if(cosinus >= 0)"                                                    +"\n"+
							"	{"                                                                   +"\n"+
							"		return asin(AbsSinus);//IAO,AbsSinus,false alarm"                   +"\n"+
							"	}"                                                                   +"\n"+
							"	return 0.0;"                                                         +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"OK"
							,
				},
				/////////////////////////28/////////////////////////////////////////////
				{
					"int i;"                                                               +"\n"+
							"void f(){"                                                            +"\n"+
							"   i=0;"                                                              +"\n"+
							"}"                                                                    +"\n"+
							"void f1(){"                                                           +"\n"+
							"  int j;"                                                             +"\n"+
							"  f();"                                                               +"\n"+
							"  j=1/i; //DEFECT"                                                    +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"IAO"
							,
				},

				/////////////////////////29/////////////////////////////////////////////
				{
					"int i;"                                                               +"\n"+
							"void f(){"                                                            +"\n"+
							"   i=0;"                                                              +"\n"+
							"}"                                                                    +"\n"+
							"void f1(){"                                                           +"\n"+
							"  int j;"                                                             +"\n"+
							"  f();"                                                               +"\n"+
							"  j=1/i; //DEFECT"                                                    +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"IAO"
							,
				},
				/////////////////////////30/////////////////////////////////////////////
				{
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
					"	return atan2(g_val1, g_val2); //DEFECT"                              +"\n"+
					"}"                                                                    
					,
					"gcc"
					,
					"IAO"
					,
				},


				////////////////////////31////////////////////////////////////////////
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
							"IAO"
							,
				},


				////////////////////////32////////////////////////////////////////////
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


				////////////////////////33////////////////////////////////////////////
				{
					"int i;"                                                               +"\n"+
							"void f(){"                                                            +"\n"+
							"   i=0;"                                                              +"\n"+
							"}"                                                                    +"\n"+
							"void f1(){"                                                           +"\n"+
							"  int j;"                                                             +"\n"+
							"  f();"                                                               +"\n"+
							"  j=1/i; //DEFECT"                                                    +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"IAO"
							,
				},

				/////////////////////////////////34////////////////////////////////////////////////////////
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
							"void ZX_IAO_FC_5_f3() //记录IAO函数信息[global != 0]"                       +"\n"+
							"{"                                                                    +"\n"+
							"	ZX_IAO_FC_5_f1();"                                                   +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_5_f4()"                                                +"\n"+
							"{"                                                                    +"\n"+
							"	ZX_IAO_FC_5_global = 0;"                                             +"\n"+
							"}"                                                                    +"\n"+
							""                                                                     +"\n"+
							"void ZX_IAO_FC_5_f5()"                                                +"\n"+
							"{"                                                                    +"\n"+
							"	ZX_IAO_FC_5_f4();"                                                   +"\n"+
							"	ZX_IAO_FC_5_f3(); //DEFECT "                                         +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"IAO"
							,
				} ,
				///////////////// 35   ///////////////////	
				//jdh  需要修改  zl
				//36,zl,已修改，同时也可以将i的约束信息传递出去
				{
					"void f(int i){"                                                       +"\n"+
							"     if(i==0){"                                                       +"\n"+
							"     }      "                                                         +"\n"+
							"     int j=1/i;"                                                      +"\n"+
							"}"                                                                    
							,
							"gcc"
							,
							"IAO"
							,
				},
/////////////////  36   ///////////////////	
	            {//区间合并,a.a的区间为unknown
	            "struct A_2_4 {"                                                       +"\n"+
	            "	int a;"                                                              +"\n"+
	            "};"                                                                   +"\n"+
	            "int foo_2_4(struct A_2_4 a, int i, int j) {"                          +"\n"+
	            "	if (i)"                                                              +"\n"+
	            "		a.a=0;"                                                             +"\n"+
	            "	if(j)"                                                               +"\n"+
	            "		10 % a.a;"                                                          +"\n"+
	            "	return 0;"                                                           +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "IAO"
	            ,
	            },
/////////////////  37   ///////////////////	
	            {
	            "struct A_2_1 {"                                                       +"\n"+
	            "	int a;"                                                              +"\n"+
	            "};"                                                                   +"\n"+
	            "int foo_2_1() {"                                                      +"\n"+
	            "	struct A_2_1 a;"                                                     +"\n"+
	            "	a.a = 0;"                                                            +"\n"+
	            "	10 % a.a;"                                                           +"\n"+
	            "	return 0;"                                                           +"\n"+
	            "}"                                                                    
	            ,
	            "gcc"
	            ,
	            "IAO"
	            ,
	            },
/////////////////  38   ///////////////////	
	            {
	            "int foo_1_8(int a, int i) {"                                                       +"\n"+
	            "10 % a;"                                                              +"\n"+
	            "if (i == 1 && a == 0) ;"                                                                   +"\n"+
	            "	return 0;"                                                           +"\n"+
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
