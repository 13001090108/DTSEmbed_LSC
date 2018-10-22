#include <string.h>

void zk_npd_17_f1()
{
	char *des = NULL;
	char *src = NULL;

	strxfrm(des, src, 5); //DEFECT
	return;
}

void zk_npd_17_f2()
{
	char des[10];
	char src[] = "sample";

	strxfrm(des, src, sizeof(src)); //FP
	return;
}