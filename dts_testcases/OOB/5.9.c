#include <stdlib.h>
int *alloc_5_9() {
	return (int *)malloc(sizeof(int) * 5);
}
int foo_5_9() {
	if (alloc_5_9()[5] == 0) ;
	return 0;
}
