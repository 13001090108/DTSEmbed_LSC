#include <stdio.h>

void zk_npd_18_f1()
{
	FILE *fp;

	fp = tmpfile();
	fputc((int)'a', fp); //DEFECT
	return;
}

void zk_npd_18_f2()
{
	FILE *fp;
	fp = tmpfile();
	if (fp != NULL)
		fputc((int)'a', fp); //FP
	return;
}