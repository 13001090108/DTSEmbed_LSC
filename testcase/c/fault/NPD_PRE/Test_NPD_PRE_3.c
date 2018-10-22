#include <stdlib.h>
void npd_1_f2(char* q)
{
	char a=*q;
}
void npd_1_f3(int a)
{
	char *p=(void*)0;
	npd_1_f2(p);  //defect
}
