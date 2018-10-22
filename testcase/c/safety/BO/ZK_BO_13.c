#include <string.h>

void zk_bo_13_f1()
{
	char buf[10];
	char *str = "This is a sample";

	strcpy(buf, str); //DEFECT
	return;
}
