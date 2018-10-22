#include <stdlib.h>
int *alloc_5_8() {
	return (int *)malloc(sizeof(int) * 5);
}
int foo_5_8(int i) {
	alloc_5_8()[5] = 0;
	if (alloc_5_8() || i) ;
	return 0;
}
