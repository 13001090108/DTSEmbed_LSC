#include <stdlib.h>

void zk_npd_15_f1()
{
	char *str = NULL;

	strtoul(str, NULL, 2); //DEFECT
	return;
}

void zk_npd_15_f2()
{
	char str[] = "2009 123";

	strtoul(str, NULL, 10); //FP
	return;
}