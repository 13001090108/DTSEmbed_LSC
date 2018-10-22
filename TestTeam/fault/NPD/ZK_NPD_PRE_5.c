#include <stdio.h>

int g_val = 3;
int *g_ptr = &g_val;

void func2(bool);

int func1()
{
	*g_ptr = 2; //FP
	func2(true);
	return *g_ptr; //DEFECT
}

void func2(bool flag)
{
	if (flag) {
		g_ptr = NULL;
	} else {
		return;
	}
}