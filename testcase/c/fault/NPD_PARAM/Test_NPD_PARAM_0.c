#include <stdlib.h>
char* ghx_npd_1_f1(int b)
{
	char * p = NULL;
	return p;
}
void ghx_npd_1_f2(char* p)
{
	char a=*p;
}
void ghx_npd_1_f3(int a)
{
	ghx_npd_1_f2(ghx_npd_1_f1(a));  //defect
}
