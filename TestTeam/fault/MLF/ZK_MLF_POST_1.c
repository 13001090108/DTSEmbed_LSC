#include <stdlib.h>

char* func2(int);
char* func3();

void func1(int flag)
{
	char *ptr;

	ptr = func2(flag);
	if (ptr) {
		*ptr = 3;
	}
	return; //DEFECT
}

char* func2(int flag)
{
	char *ptr = NULL;

	if (flag > 0) {
		ptr = (char*)malloc(sizeof(char));
	} else {
		ptr = func3();
	}

	return ptr;
}

char* func3()
{
	char *ptr;

	ptr = (char*)malloc(5*sizeof(char));
	if (ptr) {
		return ptr;
	} else {
		return NULL;
	}
}