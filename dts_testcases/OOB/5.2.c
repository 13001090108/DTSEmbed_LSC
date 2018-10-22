#include <stdlib.h>
int *alloc_5_2() {
	return (int *)malloc(sizeof(int) * 5);
}
int foo_5_2() {
	if (alloc_5_2())
		alloc_5_2()[5] = 0;
	return 0;
}
