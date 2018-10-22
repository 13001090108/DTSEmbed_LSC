#include <string.h>

void func()
{
	char *ptr1 = NULL;
	char *ptr2 = NULL;

	memcmp(ptr1, ptr2, 1); //DEFECT
}