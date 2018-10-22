#include <string.h>
#include <stdio.h>

void zk_npd_10_f1()
{
	char *str = NULL;
	char *pch;

	pch = strrchr(str, 's'); //DEFECT
	printf("%c", *pch); //DEFECT
	return;
}

void zk_npd_10_f2()
{
	char str[] = "This is a sample";
	char *pch;

	pch = strrchr(str, 's'); //FP
	if (pch)
		printf("%c", *pch); //FP
	return;
}