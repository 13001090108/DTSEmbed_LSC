#include <string.h>

void f1()
{
	char buffer2[15]="1234567890",buffer1[10],*p1=buffer1,*p2=buffer2;
	strcpy (buffer1,p2);//DEFECT
	strcpy (p1,buffer2);//DEFECT
	
}
