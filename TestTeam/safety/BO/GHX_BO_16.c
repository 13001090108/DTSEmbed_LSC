#include <stdio.h>
int ghx_bo_16_f16()
{
char overflown_buf[20];
gets(overflown_buf);//DEFECT
gets(overflown_buf+1);//DEFECT
return 0;
}