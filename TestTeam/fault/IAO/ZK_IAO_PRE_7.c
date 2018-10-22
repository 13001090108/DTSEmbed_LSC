#include <math.h>

int g_val1 = 0;
int g_val2 = 0;

void func2();
int func3();

void func1()
{
	func3();
	func2();
	func3();
}

void func2()
{
	g_val1 = g_val2 = 1;
}

int func3()
{
	return atan2(g_val1, g_val2); //DEFECT
}