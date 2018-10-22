#include <stdlib.h>
#include <string.h>

void func()
{
	char str[] = "string";
	char *ptr;
	char tmp;

	ptr = (char*)memchr(str,'p',strlen(str));
	tmp = *ptr; //DEFECT
}