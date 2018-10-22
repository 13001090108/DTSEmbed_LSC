#include <stdio.h>

void f1(char *p)
{
	
	scanf("%12s",p);
}
void f2()
{
	char buffer[10],*p=buffer;
	f1(p);//DEFECT
}
