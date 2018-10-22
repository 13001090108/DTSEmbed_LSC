#include <stdlib.h>
char* ghx_npd_1_f1(int b)
{
	if(b)
		return NULL;
	return (char*)malloc(10);
}
void ghx_npd_1_f2(char* p)
{
	char a=*p;
}
void ghx_npd_1_f3(int a)
{
	char *p=ghx_npd_1_f1(a);
	ghx_npd_1_f2(p);  //defect
}
