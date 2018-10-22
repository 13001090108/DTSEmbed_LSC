#include<string.h>
#include<stdio.h>
#include<stdlib.h>
char* zquote_cmd_string(char *p,int k)
{
   if(k<=0)
       return NULL;
   else
      {
          char * temp = (char *)malloc(k);
          strncpy(temp, k-1, p);
          return temp;
      } 
}
void test(char *z1,int k)
{
  if(*z1!='\0')
  {
     char *zq = zquote_cmd_string(z1,k);
     z1=zq;
     int len;
     len = strlen(z1);
  }
}
