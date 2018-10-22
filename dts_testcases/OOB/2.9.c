#include <stdlib.h>
struct A_2_9 {
	char *p;
};
struct A_2_9 a;

void alloc_2_9() {
	a.p = (int *)malloc(sizeof(int) * 5);
}

int foo_2_9() {
	alloc_2_9();
	a.p[5] = 'a';
	free(a.p);
	return 0;
}
