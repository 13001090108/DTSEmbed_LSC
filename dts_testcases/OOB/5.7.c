#include <stdlib.h>
int *alloc_5_7() {
	return (int *)malloc(sizeof(int) * 5);
}
int foo_5_7() {
	alloc_5_7()[5] = 0;
	if (alloc_5_7()) ;
	return 0;
}
