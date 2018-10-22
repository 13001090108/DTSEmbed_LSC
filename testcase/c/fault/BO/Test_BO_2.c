
#include <stdio.h>

void f1()
{
	char buffer1[10];

	gets(buffer1);//DEFECT

}
