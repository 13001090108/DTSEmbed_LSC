#include <string.h>

void func()
{
	char *ptr1 = NULL;

	strchr(ptr1, 's'); //DEFECT
}