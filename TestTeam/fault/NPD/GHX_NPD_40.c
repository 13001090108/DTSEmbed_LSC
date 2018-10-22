#include <string.h>

void func()
{
	char *ptr1 = NULL;
	char *ptr2 = NULL;

	memmove(ptr1, ptr2, 10); //DEFECT
}