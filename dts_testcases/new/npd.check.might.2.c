#include<stdio.h>
#include<stdlib.h>
#include<string.h>

void test2(char *value)
{
   if(sscanf(value, "%4s",buf)!=1)
     return;
	   char *trash = value?strdup(value):NULL;
   if(trash != NULL)
      free(trash);
}

void main()
{
   char *value = "hello world";
   test1(value);
}


