#include <string.h>

#define BUFSIZE 20

void zk_bo_6_f1(char *str)
{
	char buf[BUFSIZE];

	strcpy(buf, str); //DEFECT
	return;
}

void zk_bo_6_f2(char *str)
{
	char buf[BUFSIZE];

	if (strlen(str) >= BUFSIZE)
		return;
	strcpy(buf, str); //FP
	return;
}