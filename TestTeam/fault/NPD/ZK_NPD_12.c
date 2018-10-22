#include <string.h>
#include <stdio.h>

void zk_npd_12_f1()
{
	char *str = NULL;
	char *sub = NULL;
	char *pch;

	pch = strstr(str, sub); //DEFECT
	if (pch)
		printf("%s", pch); //FP
	return;
}

void zk_npd_12_f2()
{
	char str[] = "This is sample";
	char *pch;

	pch = strstr(str, "nothing"); //FP
	printf("%s", pch); //DEFECT
	return;
}