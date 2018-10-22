#include <stdlib.h>
#include <limits.h>

void zk_bo_2_f1(unsigned int n)
{
	int *buf;

	if (n > 1 + INT_MAX/sizeof(int))
		return;
	buf = (int*)malloc(n * sizeof(int)); //DEFECT
	free(buf);
}

void zk_bo_2_f2(unsigned int n)
{
	int *buf;

	if (n > INT_MAX/sizeof(int))
		return;
	buf = (int*)malloc(n * sizeof(int)); //FP
	free(buf);
}