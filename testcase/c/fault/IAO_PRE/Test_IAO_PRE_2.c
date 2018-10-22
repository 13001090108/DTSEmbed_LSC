#include <stdlib.h>

void f1(int a) //记录IAO函数信息
{
	div(10, a); 
}

void f2()
{
	int b = 0;
	f1(b); //DEFECT, 利用IAO函数信息
}

void f3()
{
	int b = -2;
	f1(b+2); //DEFECT, 利用IAO函数信息,
}
