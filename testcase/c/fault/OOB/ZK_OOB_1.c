#include <stdlib.h>

#define BUFSIZE 10

void zk_bo_19_f1()
{
	int *buf;

	buf = (int *)malloc(BUFSIZE * sizeof(int));
	if (buf == NULL)
		return;
	buf[BUFSIZE+1] = 1; //DEFECT
	buf[-1] = 2; //DEFECT

	*(buf+BUFSIZE) = 12; //DEFECT
	*(buf-2) = 3; //DEFECT
	free(buf);
}
