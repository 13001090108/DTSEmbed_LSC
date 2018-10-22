#include <stdlib.h>
int *alloc_5_5() {
	return (int *)malloc(sizeof(int) * 5);
}
int foo_5_5() {
	if (alloc_5_5()) ;
	alloc_5_5()[5] = 0;
	return 0;
}
