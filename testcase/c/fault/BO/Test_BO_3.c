
#include <stdio.h>

void f1()
{
	char buffer2[10],buffer1[10];
	scanf("%12s",buffer1);//DEFECT
	scanf("%8s%s",buffer1,buffer2);//DEFECF
}
