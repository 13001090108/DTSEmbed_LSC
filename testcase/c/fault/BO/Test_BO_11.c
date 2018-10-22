#include <string.h>

void f1()
{
	int a=11;
	char buffer2[15]="1234567890",buffer1[10];
	strncat (buffer1,buffer2,11);//DEFECT
	strncat (buffer1,buffer2,a);//DEFECT
}
