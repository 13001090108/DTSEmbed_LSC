#include <string.h>
void ghx_bo_15_f15()
{
char buf [20];
char long_src[30];
char *external_pointer;
strncpy(buf, long_src, 30); //DEFECT
strncpy(buf, external_pointer, sizeof(buf));//DEFECT
strncpy(buf, external_pointer, 30); //DEFECT
strncpy(buf, external_pointer, sizeof(buf)-1); //FP
}