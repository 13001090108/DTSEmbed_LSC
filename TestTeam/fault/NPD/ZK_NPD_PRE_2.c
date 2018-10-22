#include <stdlib.h>

void func2(char *);

void func1()
{
	func2(NULL); //DEFECT
}

void func2(char *var)
{
	*var = 2; 
}