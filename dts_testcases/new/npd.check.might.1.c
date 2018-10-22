#include<stdio.h>
#include<stdlib.h>
#include<string.h>

void test1(char *value)
{
	  char *trash = value?strdup(value):NULL;
   char buf[5];
   if(sscanf(value, "%4s",buf)!=1)
       free(trash);
}

void main()
{
   char *value = "hello world";
   test1(value);
}

