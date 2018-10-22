#include<stdlib.h>
void foo4()
 {
	int *a = (int *)malloc(sizeof(int)*1);
	int *b = (int *)malloc(sizeof(int)*1);
	
	if(!a || !b)
	{
		return ;
	}
	
	free(a);
	free(b);
}
