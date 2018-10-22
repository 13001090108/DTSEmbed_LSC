#include <time.h>

void func()
{
	localtime(NULL); //DEFECT
}