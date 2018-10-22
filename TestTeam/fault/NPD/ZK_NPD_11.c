#include <string.h>

char *zk_npd_11_g1 = NULL;
char *zk_npd_11_g2 = NULL;

void zk_npd_11_f1()
{
	strspn(zk_npd_11_g1, zk_npd_11_g2); //DEFECT
	return;
}

void zk_npd_11_f2()
{
	if (zk_npd_11_g1 && zk_npd_11_g2)
		strspn(zk_npd_11_g1, zk_npd_11_g2); //FP
	return;
}