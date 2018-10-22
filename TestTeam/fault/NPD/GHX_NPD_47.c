#include <stdlib.h>

void func()
{
	qsort (NULL, 6, sizeof(int), NULL);//DEFECT
}