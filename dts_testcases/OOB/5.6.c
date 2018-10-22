#include <stdlib.h>
int *alloc_5_6() {
	return (int *)malloc(sizeof(int) * 5);
}
int foo_5_6(int i) {
	if (alloc_5_6() || i) ;
	alloc_5_6()[5] = 0;
	return 0;
}
