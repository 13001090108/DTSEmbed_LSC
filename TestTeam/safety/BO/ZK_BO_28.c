#include <stdio.h>

void zk_bo_28_f1(FILE *fp)
{
	char tmp[50];

	fscanf(fp, "%20s", tmp);
	fscanf(fp, "%10s", tmp);
	fscanf(fp, "%50s", tmp); //DEFECT
}