#include <stdlib.h>
#include <string.h>
#include <io.h>
struct ghx_npd_1_s1
{
	char *ss;
};
void ghx_npd_1_f1()
{
	ghx_npd_1_s1 *s;
	s=(ghx_npd_1_s1*)malloc(sizeof(ghx_npd_1_s1));
	read(1,s,sizeof(s));//DEFECT

}
