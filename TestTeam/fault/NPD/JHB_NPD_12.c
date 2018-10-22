#include <stdlib.h>
#include <stdio.h>
char* jhb_npd_12_f1(int t)
{
	if (t>0)
	{
		char *c="234567890";
		return c;
	}
	return NULL;
}
void jhb_npd_12_f2(int m){
	char a[]="1000000000";
	char* b;
	b=jhb_npd_12_f1(m);
	long c;
	c=atol(a)+atol(b);     //DEFECT
	printf("c=%d\n",c);
}

