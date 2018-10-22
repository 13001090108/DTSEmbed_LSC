#include <string.h>
#include <stdio.h>
int ghx_npd_14_f14()
{
char *str1=NULL;
char *str2=NULL;
memmove(str1,str2,10);//DEFECT
return 0;

}

int ghx_npd_14_f13()
{
char *dest = "abcdefghijklmnopqrstuvwxyz0123456789"; 
char *src = "******************************"; 

memmove(dest, src, 26); //FP
printf("%s\n", dest); 
return 0; 
}