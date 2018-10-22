#include <stdio.h>

void func()
{
	char *ptr1 = NULL;
	char *ptr2 = NULL;

	rename(ptr1, ptr2); //DEFECT
}