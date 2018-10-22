#include <stdlib.h>
#include <string.h>
struct ghx_npd_5_s5
{
	char* ss;
	
};
void ghx_npd_5_f5()
{
	ghx_npd_5_s5 s;
	s.ss=(char*)malloc(10);
	char* a=(char*)malloc(10);
	s.ss[0]=*a;//DEFECT
}
