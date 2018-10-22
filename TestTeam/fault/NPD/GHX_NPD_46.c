#include <stdio.h>

void func()
{
	char *ptr1 = NULL;

	puts(ptr1); //DEFECT
}