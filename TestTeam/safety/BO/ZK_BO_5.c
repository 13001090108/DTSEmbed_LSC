#include <stdlib.h>

void zk_bo_5_f1(unsigned int len)
{
	int *buf;
	int i;

	buf = (int *)malloc(len * sizeof(int)); //DEFECT
	if (buf == NULL)
		return;
	for (i = 0; i < n; ++i)
		buf[i] = i;

	return;
}

void zk_bo_5_f2()
{
	int n = -1;

	zk_bo_5_f1(n);
	return;
}