#include <math.h>

void func2(int&);
int func3(int);

void func1()
{
	int a;

	func2(a);
	func3(a); //DEFECT
}

void func2(int &var1)
{
	var1 = 10;
}

int func3(int var1)
{
	return asin(var1);
}