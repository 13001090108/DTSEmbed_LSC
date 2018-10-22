#include <stdlib.h>

int *p;
void alloc_1_9() {
	p = (int *)malloc(sizeof(int) * 5);
}

int foo_1_9() {
	alloc_1_9();
	p[5] = 'a';
	free(p);
	return 0;
}
