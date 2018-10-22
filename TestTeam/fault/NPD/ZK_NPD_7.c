#include <string.h>

void zk_npd_7_f1()
{
	char *str1 = NULL;
	char *str2 = NULL;

	strncmp(str1, str2, 5); //DEFECT
	return;
}

void zk_npd_7_f2()
{
	char *str1 = "hello world";
	char *str2 = "hello";

	strncmp(str1, str2, 5); //FP
	return;
}