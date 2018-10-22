#include <time.h>

void func()
{
	mktime(NULL); //DEFECT
}