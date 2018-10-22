#include <stdio.h>

void f1()
{
	char buffer2[10],buffer1[10],*p1=buffer1,*p2=buffer2;
	scanf("%12s",p1);//DEFECT
	scanf("%8s%s",buffer1,p2);//DEFECF
}
