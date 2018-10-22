#include <stdlib.h>

void zk_npd_26_f1(wchar_t wc)
{
	wctomb(NULL, wc); //DEFECT
	return;
}

void zk_npd_26_f2(char *mb, wchar_t wc)
{
	if (mb == NULL)
		return;
	wctomb(mb, wc); //FP
	return;
}