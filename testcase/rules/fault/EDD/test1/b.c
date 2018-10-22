#include <stdio.h>

extern char r;

double b;
double circle();

void main()
{
		extern char a;    
        a=3;
    	r=2;
	printf("the area is %f\n",circle());
	
}
