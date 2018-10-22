#include <stdlib.h>

int global;

void f1() //记录IAO函数信息[global != 0]
{
	div(10, global); 
}

void f2()
{
	global = 0;
	f1(); //DEFECT, 利用IAO函数信息
}

void f3() //记录IAO函数信息[global != 0]
{
	f1();
}

void f4()
{
	global = 0;
}

void f5()
{
	f4();
	f3(); //DEFECT 
}
