#include <string.h>

void zk_npd_1_f1(char *str1, char *str2)
{
	strcoll(str1, str2); //DEFECT
	return;
}

void zk_npd_1_f2()
{
	char *str1 = "This is first";
	char *str2 = "Second";

	strcoll(str1, str2); //FP
}