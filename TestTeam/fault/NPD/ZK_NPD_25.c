#include <stdlib.h>

void zk_npd_25_f1()
{
	wcstombs(NULL, NULL, 0); //DEFECT
	return;
}

void zk_npd_25_f2(char *mbstr, wchar_t *wcstr)
{
	if (mbstr == NULL || wcstr == NULL)
		return;
	wcstombs(mbstr, wcstr, sizeof(mbstr)); //FP
	return;
}