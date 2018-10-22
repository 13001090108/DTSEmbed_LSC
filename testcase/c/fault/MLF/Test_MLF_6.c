#include<stdlib.h>
void foo2(int a)
 {
	int *p= (int *)malloc(sizeof(int)*1);
	
	if(a>0)
		return;
	
	free(p);
}
