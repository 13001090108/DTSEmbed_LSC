#include <stdio.h>
int jhb_npd_26_f1(void)
{
	fputs("Hello world\n", NULL);  //DEFECT
	return 0;
}
