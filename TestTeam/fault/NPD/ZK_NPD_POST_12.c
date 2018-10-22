#include <stdlib.h>

char* func2(int);
char* func3();

void func1(int flag)
{
	char *ptr;

	if (flag > 0) {
		ptr = func2(flag);
	} else {
		ptr = func3();
	}
	*ptr = 3; //DEFECT
}

char* func2(int flag)
{
	if (flag < 0) {
		return NULL;
	} else {
		func3();
	}
}

char* func3()
{
	return NULL;
}