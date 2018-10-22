#include <string.h>
#include <stdio.h>

void zk_npd_14_f1()
{
	char str[] = "This is a sample";
	char *pch;

	pch = strtok(str, NULL); //DEFECT
	printf("%s", pch); //DEFECT
	return;
}

void zk_npd_14_f2()
{
	char str[] = "This is a sample";
	char *pch;

	pch = strtok(str, " "); //FP
	while (pch != NULL)
	{
		printf("%s", pch); //FP
		strtok(NULL, " "); //FP
	}
	printf("%s", pch); //DEFECT
	return;
}