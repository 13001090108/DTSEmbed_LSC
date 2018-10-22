#include <string.h>
#include <stdio.h>
int ghx_npd_15_f15()
{
char *str=NULL;
memset(str,'*',6);//DEFECT
return 0;
}

int ghx_npd_15_f14()
{
char str[]="welcome to beijing";
memset(str,'*',7);//FP
printf("%s\n",str);
return 0;
}