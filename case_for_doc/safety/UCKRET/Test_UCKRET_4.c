#include <string.h>
#include <stdlib.h>
int ghx_uckret_1_f1()
{
	char *buf;
	char *xfer="abc";
	int req_size=10;
buf = (char*) malloc(req_size);//DEFECT
strncpy(buf, xfer, req_size);
return 0;
}