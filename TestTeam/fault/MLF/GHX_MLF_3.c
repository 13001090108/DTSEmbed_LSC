#include "stdlib.h"
void ghx_mlf_3_f3()
{
	int *m=NULL;
	if((m=(int*)malloc(100))!=NULL)
	{
		return;//DEFECT
	}
}
