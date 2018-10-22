#include <stdio.h>

void zk_npd_31_f1(char *pathname)
{
	FILE *fp;

	fp = fopen(pathname, "a");
	fprintf(fp, "Acess file"); //DEFECT
	return;
}