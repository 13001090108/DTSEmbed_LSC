#include <stdlib.h>

void zk_npd_15_f1()
{
	char *str = NULL;

	strtol(str, NULL, 2); //DEFECT
	return;
}

void zk_npd_15_f2()
{
	char str[] = "2009 123";

	strtol(str, NULL, 10); //FP
	return;
}