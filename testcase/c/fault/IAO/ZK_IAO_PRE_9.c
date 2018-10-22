#include <math.h>

void func1(int var)
{
	func2(var);
}

int func2(int var)
{
	if (var < 0) {
		return func3(var); //DEFECT
	} else {
		return 0;
	}
}

int func3(int var)
{
	return sqrt(var);
}
