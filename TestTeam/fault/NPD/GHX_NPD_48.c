#include <string.h>

void func()
{
	char *ptr = NULL;

	memset(ptr,'*',6);//DEFECT
}