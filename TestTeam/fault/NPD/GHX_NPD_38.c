#include <stdio.h>

void func()
{
	char *ptr = NULL;

	perror(ptr); //DEFECT
}