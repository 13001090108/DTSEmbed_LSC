#include <stdio.h>

int ghx_bo_7_f7() 
{
	char str[16];
	_snprintf(str, 20, "%s %d", "hello worldxxxx", 1000);//DEFECT
	return 0;
}