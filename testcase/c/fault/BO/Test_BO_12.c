#include <string.h>

void f1()
{
	char buffer1[10],*p=buffer1;
	strcpy (p,"1234567890");//DEFECT
	
}
