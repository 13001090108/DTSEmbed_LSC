#include <string.h>
#include <stdlib.h>

#define MAXSIZE 1024

void zk_npd_2_f1()
{
	char *str1 = NULL;
	char *str2 = (char*)malloc(MAXSIZE);

	if (!str2)
		return;
	strcpy(str2, str1); //DEFECT
	return;
}

void zk_npd_2_f2(char *str1, char *str2)
{
	if (!str1 || !str2)
		return;
	strcpy(str1, str2);
	return;
}