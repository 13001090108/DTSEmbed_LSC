#include <string.h>

void zk_bo_22_f1()
{
	char buf[10];

	strcpy(buf, "AAAAAAAAAAAA"); //DEFECT
	return;
}
