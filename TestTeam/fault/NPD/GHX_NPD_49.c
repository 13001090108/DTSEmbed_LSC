#include <string.h>

void func()
{
	char *ptr1 = NULL;
	char *ptr2 = NULL;

	memcpy(ptr1, ptr2, 6);//DEFECT
}