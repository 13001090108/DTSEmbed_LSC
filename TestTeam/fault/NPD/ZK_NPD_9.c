#include <string.h>
#include <stdio.h>

void zk_npd_9_f1()
{
	char *str1, *str2;
	str1 = NULL;
	str2 = NULL;

	strpbrk(str1, str2); //DEFECT
	return;
}

void zk_npd_9_f2()
{
	char *pch;
	char str[] = "This is sample";
	char key[] = "xyz";

	pch = strpbrk(str, key); //FP
	printf("%c", *pch); //DEFECT

	if (pch)
		printf("%c", *pch); //FP
	return;
}