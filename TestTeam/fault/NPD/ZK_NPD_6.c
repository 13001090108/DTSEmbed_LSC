#include <string.h>

void zk_npd_6_f1()
{
	char *des = NULL;
	char *src = NULL;

	strncat(des, src, 4); //DEFECT
	return;
}

void zk_npd_6_f2()
{
	char des[10] = "This";
	char src[10] = "is it and";

	strncat(des, src, 5); //FP
	return;
}