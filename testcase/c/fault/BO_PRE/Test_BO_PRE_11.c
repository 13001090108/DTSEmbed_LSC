#include <string.h>

void f1(char *p)
{
	char buffer2[15]="1234567890";
	strcpy (p,buffer2);
	
}
void f2()
{
	char buffer[10];
	f1(buffer);//DEFECT
}
