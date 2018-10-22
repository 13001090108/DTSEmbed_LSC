#include <stdio.h>
#include <stdlib.h>

void zk_npd_35_f1()
{
	char *key;

	key = (char *)malloc(sizeof(char)*10);
	sprintf(key, "char"); //DEFECT
	return;
}