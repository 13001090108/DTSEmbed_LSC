#include <stdio.h>
void ghx_bo_14_f14()
{
char str[4]="abc";
gets(str);//DEFECT
printf(str);/*fault belongs to TD*/
}