#include <stdlib.h>
#include <string.h>

void func()
{
	int i = 1;
	char *ptr;

	ptr = (char*)malloc(i+1);
	memchr(ptr,'p',10); //DEFECT
}