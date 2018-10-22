#include <stdlib.h>

int *p[5];
void alloc_4_9() {
	p[0] = (int *)malloc(sizeof(int) * 5);
}

int foo_4_9() {
	alloc_4_9();
	p[0][5] = 'a';
	free(p[0]);
	return 0;
}
