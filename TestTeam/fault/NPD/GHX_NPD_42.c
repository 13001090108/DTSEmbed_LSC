#include <stdio.h>

void func()
{
	char *ptr1 = NULL;
	char *ptr2 = NULL;
	int m = 2;

	sscanf (ptr1,"%s %*s %d", ptr2,&m); //DEFECT
}