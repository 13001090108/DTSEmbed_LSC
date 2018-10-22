#include <stdio.h>

void func()
{
	char *ptr = NULL;
	int i = 1, j = 2;

	sprintf (ptr, "%d plus %d is %d", i, j, i+j);//DEFECT
}