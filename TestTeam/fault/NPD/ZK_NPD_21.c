#include <stdio.h>

void zk_npd_21_f1()
{
	char *ptr;

	ptr = tmpnam(NULL); //FP
	printf("Tmpname: %s", ptr);
	return;
}