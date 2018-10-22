#include <string.h>

void zk_npd_3_f1()
{
	char *str1 = NULL;
	char *str2 = NULL;

	strcspn(str1, str2); //DEFECT
	return;
}

void zk_npd_3_f2()
{
	char *str1 = "abcdefg";
	char *str2 = "gh";

	strcspn(str1, str2); //FP
	return;
}