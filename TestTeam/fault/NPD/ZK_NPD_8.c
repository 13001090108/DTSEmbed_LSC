#include <string.h>

void zk_npd_8_f1()
{
	char *des = NULL;
	char *src = NULL;

	strncpy(des, src, 4); //DEFECT
	return;
}

void zk_npd_8_f2()
{
	char des[10];
	char src[] = "This is a sample";

	strncpy(des, src, 7); //FP
	des[7] = '\0';
	return;
}