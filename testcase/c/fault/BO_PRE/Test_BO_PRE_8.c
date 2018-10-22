#include <string.h>

void f1(int a)
{
	char buffer2[a],buffer1[10];
	strcpy (buffer1,"123456789");
	strcpy (buffer2,buffer1);
	
}
void f2(int a)
{
	
	f1(a);//DEFECT
}

void f3()
{
	int a=9;
	f2(a);
}
