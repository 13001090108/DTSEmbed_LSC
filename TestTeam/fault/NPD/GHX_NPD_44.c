#include <string.h>

void func()
{
	char *ptr1 = NULL;
	char *ptr2 = NULL;

	strcmp(ptr1, ptr2); //DEFECT
}