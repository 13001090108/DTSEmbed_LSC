#include <stdio.h>

void f1(char *p)
{
	char buffer1[10]="welcome",buffer2[10]="to china!";
	sprintf(p,"%8s%8s",buffer1,buffer2);
	
}
void f2(char *p)
{
	
	sprintf(p,"%8d%8d",123,345);
	
}
void f3(char *p)
{
	char buffer1[10]="welcome",buffer2[10]="to china!",buffer3[10];
	
	sprintf(buffer3,"%8s%8s",buffer1,p);
}
void f4()
{
	char buffer1[10]="welcome",buffer2[10]="to china!",buffer3[10];
	char *p1=buffer1,*p2=buffer2,*p3=buffer3;
	f1(p3);//DEFECT
	f2(p1);//DEFECT
	f3(p2);
}
