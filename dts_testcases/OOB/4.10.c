#include <stdlib.h>
int *p[5];
void alloc_4_10() {
	p[0] = (int *)malloc(sizeof(int) * 5);
}
void callAlloc_4_10() {
	alloc_4_10();
}
int foo_4_10() {
	callAlloc_4_10();
	p[0][5] = 'a';
	free(p[0]);
	return 0;
}
