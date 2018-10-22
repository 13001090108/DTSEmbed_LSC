#include <string.h>
#include <stdio.h>

void zk_bo_26_f1()
{
	char buf1[121];
	char buf2[16];
	int i;

	for (i = 0; i < 121; i++) {
		buf1[i] = getchar();
	}
	strcpy(buf2, buf1); //DEFECT
	printf("%s\n", buf1);
	printf("%s\n", buf2);
	return;
}