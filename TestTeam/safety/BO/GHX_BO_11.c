#include <io.h>
#include <string.h>
void ghx_bo_11_f11()
{
char src[32];
char dst[48];
read(0, src, sizeof(src));
strcpy(dst, src);//DEFECT
}