#include <string.h>

void f1()
{
	char buffer1[10];
	strcpy (buffer1,"1234567890");//DEFECT
	
}
