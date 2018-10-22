#include <stdlib.h>

void func2(float*);

void func1()
{
	float *ptr = NULL;

	ptr = (float*)malloc(sizeof(float));
	func2(ptr); //DEFECT
	if (ptr)
	{
		free(ptr);
	}
}

void func2(float *var)
{
	*var = 0.1f;
}