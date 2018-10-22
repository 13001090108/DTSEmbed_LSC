#include <stdio.h>
#include <string.h>
int ghx_bo_6_f6()
{
char str1[100];
char str2[50];
memcpy(str2,str1,(sizeof(str1)));//DEFECT
return 0;
}

#include <stdio.h>
int ghx_bo_6_f5()
{
char str1[100];
char str2[50];
memcpy(str2,str1,(sizeof(str2)));//FP
return 0;
}