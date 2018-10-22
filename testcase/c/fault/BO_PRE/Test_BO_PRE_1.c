#include <stdio.h>

void f1(int a)
{
	char buffer1[10]="welcome",buffer2[10]="to china!",buffer3[a];
	sprintf(buffer3,"%8s%8s",buffer1,buffer2);
	
}
void f2(int a)
{
	char buffer3[a];
	
	sprintf(buffer3,"%8d%8d",123,345);
	
}
void f3(int a)
{
	char buffer1[10]="welcome",buffer2[10]="to china!",buffer3[a];
	
	sprintf(buffer3,"%s%8s",buffer1,buffer2);//DEFECT
}
void f4()
{
	int a=15;
	f1(a);//DEFECT
	f2(a);//DEFECT
	f3(a);
}
