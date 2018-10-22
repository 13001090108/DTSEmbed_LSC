#include <string.h>

void zk_npd_5_f1(char *str)
{
	strlen(str); //DEFECT
	return;
}

void zk_npd_5_f2(char *str)
{
	if (!str)
		return;
	strlen(str); //FP
	return;
}