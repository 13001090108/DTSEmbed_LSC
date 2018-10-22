#include<stdlib.h>
int *foo11(int size)
{
	int *a = (int *)malloc(sizeof(int)*size);
	
	return a;
}

void foo10()
{
	int size = 1;
	int *a = foo11(size);
}
