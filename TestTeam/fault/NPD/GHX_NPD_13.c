#include <string.h>
#include <stdio.h>
int ghx_npd_13_f13(char *str5,char*str6)
{
char *str1=NULL;
char *str2=NULL;
char *str3="abcedfg";
char *str4[40];
memcpy(str1,str3,7);  //DEFECT
memcpy(str4,str2,10);  //DEFECT
memcpy(str5,str6,strlen(str6)); //DEFECT
return 0;
}

int ghx_npd_13_f12 ()
{
  char str1[]="Sample string";
  char str2[40];
  char str3[40];
  memcpy (str2,str1,strlen(str1)+1);//FP
  memcpy (str3,"copy successful",16);//FP
  printf ("str1: %s\nstr2: %s\nstr3: %s\n",str1,str2,str3);
  return 0;
}
