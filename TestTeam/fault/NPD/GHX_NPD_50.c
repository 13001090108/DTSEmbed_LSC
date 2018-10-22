#include <math.h>
#include <stdlib.h>

void func()
{
	double a;
	double *b=NULL;
	double c=100000.567;

	a = modf(c,b);//DEFECT
}