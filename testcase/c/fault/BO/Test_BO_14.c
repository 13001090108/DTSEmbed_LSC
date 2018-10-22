

#include <string.h>

void f1()
{
	int a=6;
	char buffer2[10]="WELCOME",buffer1[5],*p1=buffer1,*p2=buffer2;
	strncat(p1,buffer2,6);//DEFECT
	strncat(p1,buffer2,5);//DEFECT
	strncat(buffer1,p2,a);//DEFECT
}
