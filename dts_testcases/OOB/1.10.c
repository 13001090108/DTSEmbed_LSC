#include <stdlib.h>
int *p;
void alloc_1_10() {
	p = (int *)malloc(sizeof(int) * 5);
}
void callAlloc_1_10() {
	alloc_1_10();
}
int foo_1_10() {
	callAlloc_1_10();
	p[5] = 'a';
	free(p);
	return 0;
}
