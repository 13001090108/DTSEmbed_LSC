#include <stdlib.h>

void func()
{
	int i = 1;
	char *ptr;

	ptr = (char*)malloc(i+1);
	ptr[i]='\0';//DEFECT
}