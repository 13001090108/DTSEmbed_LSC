#include <stdlib.h>
char* npd_1_f1()
{
	return (void*)0;
}
void npd_1_f2(char* q)
{
	char a=*q;
}
void npd_1_f3()
{
	char *p=npd_1_f1();
	npd_1_f2(p);  //defect
}
