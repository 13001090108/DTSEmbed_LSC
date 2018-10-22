#include <stdlib.h>

void zk_npd_32_f1(int num, int *ptr)
{
	*ptr = num;
	return;
}

void zk_npd_32_f2()
{
	int val = 32;
	int *ptr;

	ptr = (int *)malloc(sizeof(int));
	zk_npd_32_f1(val, ptr); //DEFECT

	if (ptr)
		free(ptr);
	return;
}