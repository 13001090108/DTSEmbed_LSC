#include <stdio.h>

void zk_bo_22_f1()
{
	char buf[128];

	fscanf(stdin, "%s", buf); //DEFECT
	return;
}
