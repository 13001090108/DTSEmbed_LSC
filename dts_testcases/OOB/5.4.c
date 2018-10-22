#include <stdlib.h>
int *alloc_5_4() {
	return (int *)malloc(sizeof(int) * 5);
}
int bar_5_4(int i, int j) {
	if (i)
		alloc_5_4();
	if (j)
		alloc_5_4()[5] = 0;
	return 0;
}
