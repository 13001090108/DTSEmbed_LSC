#include <string.h>

void f1(int a)
{
	char buffer2[15]="1234567890",buffer1[a];
	strcpy (buffer1,buffer2);
	
}
void f2()
{
	int a=10;
	f1(a);//DEFECT
}
