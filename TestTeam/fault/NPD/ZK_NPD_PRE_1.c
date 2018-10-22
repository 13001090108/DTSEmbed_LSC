#include <stdlib.h>

void func2(char *);
void f(int, char*);

void func1(int flag)
{
	char *ptr = NULL;

	ptr = (char*)malloc(sizeof(char));
	f(flag,ptr); //DEFECT
	if (ptr)
	{
		free(ptr);
	}
}

void f(int flag,char* var)
{
	if(flag) {
    	func2(var);
    } else {
		*var = 3;
    }
}

void func2(char *var)
{
	*var = 2;
}