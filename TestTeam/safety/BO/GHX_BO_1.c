#include <string.h>
void GHX_BO_1_f1(char p[420])
{
	char buffer [400];
	strcpy (buffer,"welcome to beijing ");//FP
	strcat (buffer, p);//DEFECT
}