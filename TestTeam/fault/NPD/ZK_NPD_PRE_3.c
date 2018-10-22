#include <stdlib.h>

int g_val = 1;

void func2(int, char *);
void func3(char *, int);
void func4(int, char *, int);

void func1()
{
	char *ptr;

	ptr = NULL;
	func2(1, ptr); //DEFECT
}

void func2(int val, char *var)
{
	func3(var, val);
}

void func3(char *var, int val)
{
	func4(val, var, g_val);
}

void func4(int val, char *var, int flag)
{
	if (flag > 0) {
		*var = val;
	} else {
		return;
	}
}