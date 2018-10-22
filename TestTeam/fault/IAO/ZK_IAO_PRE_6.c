#include <math.h>

int func2(bool, int);
int func3(int);

void func1(bool flag, int a)
{
	if (a >= -1 && a <= 1) {
		func2(flag, a);
	} else {
		func2(flag, a); //DEFECT
	}
}

int func2(bool flag, int var1)
{
	if (flag) {
		return acos(var1);
	} else {
		return func3(var1);
	}
}

int func3(int var1)
{
	return acos(var1);
}