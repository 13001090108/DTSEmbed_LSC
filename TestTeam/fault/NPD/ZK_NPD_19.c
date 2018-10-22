#include <stdio.h>

void zk_npd_19_f1(char c)
{
	FILE *fp = NULL;

	ungetc(c, fp); //DEFECT
	return;
}

void zk_npd_19_f2(FILE *fp)
{
	if (fp == NULL)
		return;
	ungetc((int)'a', fp); //FP
	return;
}