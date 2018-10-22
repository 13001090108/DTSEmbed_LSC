#include <stdlib.h>
char* npd_1_f1(int b)
{
	char * p = NULL;
	return p;
}
void npd_1_f2(char* q)
{
	char a=*q;
}
void npd_1_f3(int a)
{
	char *p=npd_1_f1(a);
	npd_1_f2(p);  //defect
}
