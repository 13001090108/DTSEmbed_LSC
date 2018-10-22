#include <stdlib.h>

int g_val = 1;

void func2(int, double*);
void func3(double*, int);
void func4(int, double*, int);

void func1()
{
	double *ptr;

	ptr = NULL;
	func2(1, ptr); //DEFECT
}

void func2(int val, double *var)
{
	func3(var, val);
}

void func3(double *var, int val)
{
	func4(val, var, g_val);
}

void func4(int val, double *var, int flag)
{
	if (flag > 0) {
		*var = val;
	} else {
		return;
	}
}