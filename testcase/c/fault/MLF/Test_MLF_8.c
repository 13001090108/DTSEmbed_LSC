#include<stdlib.h>
void foo5()
 {
	int *a = (int *)malloc(sizeof(int)*10);
	a++;
	free(a);
}
