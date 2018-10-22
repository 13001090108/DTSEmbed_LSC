#include <string.h>

void f1(char *p)
{
	char buffer2[15];
	strcpy (buffer2,"1234567890");
	strcpy (p,buffer2);
	
}
void f2(char *p)
{
	
	f1(p);//DEFECT
}

void f3()
{	char buffer[10];
	//char *p=buffer;
	f2(buffer);
}
