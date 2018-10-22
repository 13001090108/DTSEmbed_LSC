#include <stdio.h>
void ghx_oob_10_f10()
{
char b[8];
int a=1;
int c=0;
if(a>0)
{
c++;
b[c]=0;//FP
}
printf("%d\n",c);
}