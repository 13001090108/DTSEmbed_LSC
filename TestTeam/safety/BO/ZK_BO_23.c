#include <string.h>
#include <stdio.h>

void zk_bo_23_f1()
{
	char src[] = "ThisisSample";
	char des[6];

	strncpy(des, src, 6); //DEFECT
	printf("%s", des);
	return;
}