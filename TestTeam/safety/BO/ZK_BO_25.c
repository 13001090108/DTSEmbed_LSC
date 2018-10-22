#include <stdio.h>

void zk_bo_25_f1()
{
	char buf1[12];
	char buf2[12];
	char des[16];

	fgets(buf1, sizeof(buf1), stdin);
	fgets(buf2, sizeof(buf2), stdin);

	sprintf(des, "%s-%s", buf1, buf2); //DEFECT
	return;
}