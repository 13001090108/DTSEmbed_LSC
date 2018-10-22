#include <string.h>

void f1()
{
	char buffer2[15]="1234567890",buffer1[10];
	strcpy (buffer1,buffer2);//DEFECT
	
}
