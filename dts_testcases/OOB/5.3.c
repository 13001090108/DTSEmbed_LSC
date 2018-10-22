#include <stdlib.h>
int *alloc_5_3() {
	return (int *)malloc(sizeof(int) * 5);
}
int foo_5_3(int i) {
	if (alloc_5_3() || i)
		alloc_5_3()[5] = 0;
	return 0;
}
