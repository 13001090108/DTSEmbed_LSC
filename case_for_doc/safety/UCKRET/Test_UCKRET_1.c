
#include <stdlib.h>
#include <stdio.h>

int yxh_UCKRET_f_1 ()
{
	int *p;
	if ((p = (int *)malloc(4)) != NULL)//OK
	{
		*p = 4;
	}

	return 0;
}
