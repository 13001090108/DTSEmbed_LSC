#include <stdlib.h>
int *alloc_5_10() {
	return (int *)malloc(sizeof(int) * 5);
}
int foo_5_10(int i) {
	if (i || alloc_5_10()[5] == 0) ;
	return 0;
}
