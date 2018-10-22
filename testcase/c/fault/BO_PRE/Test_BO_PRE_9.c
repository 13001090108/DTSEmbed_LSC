#include <string.h>

void f1(char *p)
{
	char buffer2[15]="1234567890";
	strncat (p,buffer2,10);//DEFECT
}
void f2()
{
	char buffer1[10];
	f1(buffer1);
}
