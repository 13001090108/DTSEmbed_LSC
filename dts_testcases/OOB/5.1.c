#include <stdlib.h>
int *alloc_5_1() {
	return (int *)malloc(sizeof(int) * 5);
}
int foo_5_1() {
	alloc_5_1()[5] = 0;
	return 0;
}
