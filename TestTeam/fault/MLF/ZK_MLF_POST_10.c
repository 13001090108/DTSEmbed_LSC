#include <stdlib.h>

char* func2(int);

void func1(int flag, int size)
{
	char *ptr;

	ptr = func2(size);
	if (ptr == NULL)
		return;

	if (flag < 0) {
		ptr = NULL; //DEFECT
		return; 
	} else {
		*ptr = 3;
	}

	free(ptr);
}

char* func2(int size)
{
	char *ptr = NULL;

	ptr = (char*)malloc(size*sizeof(char));
	return ptr;
}