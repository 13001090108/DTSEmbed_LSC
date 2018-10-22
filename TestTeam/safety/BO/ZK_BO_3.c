#include <stdlib.h>
#include <limits.h>

void zk_bo_3_f1(unsigned int n)
{
	int *buf;

	buf = (int*)malloc(n * sizeof(int)); //DEFECT
	free(buf);
}

void zk_bo_3_f2()
{
	int n = -1;

	if (n * sizeof(int) <= INT_MAX)
		zk_bo_3_f1(n);
	return;
}