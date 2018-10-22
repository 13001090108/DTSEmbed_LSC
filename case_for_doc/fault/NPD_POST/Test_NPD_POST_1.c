#include <stdlib.h>
char c = 'a';
char *ptr = &c;

void func1()
{
	func2();
	*ptr = 3; //DEFECT
}
void func2()
{
	ptr =  0;
}
