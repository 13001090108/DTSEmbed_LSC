#include <stdlib.h>

void zk_npd_exp_2_f1()
{
	int *ptr;

	ptr = (int*)malloc(4 * sizeof(int));
	if (!ptr)
		return;
	*(ptr + 2) = 5; //FP
	free(ptr);
	return;
}