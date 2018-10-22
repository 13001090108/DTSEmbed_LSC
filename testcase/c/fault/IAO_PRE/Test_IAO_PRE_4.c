#include <stdlib.h>

int global;

void f1(int a) //不单是个变量，是个表达式，记录IAO函数信息[global != 0] 
{
	if(a == 0)
		div(10, global); 
	if(a == 1)
		div(10, global+3);
}

void f2()
{
	global = 0;
	f1(0); //DEFECT
}
