#include <stdlib.h>

// Array
int foo_1_1() {
	char p[5] = {0};
	p[5] = 'a';
	return 0;
}

// Memory
int bar_1_1() {
	int *p;
	p = (int *)malloc(sizeof(int) * 5);
	p[5] = 'a';
	free(p);
	return 0;
}
