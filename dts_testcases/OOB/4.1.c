#include <stdlib.h>

// Array
int foo_4_1() {
	char p[5][5] = {0};
	p[0][5] = 'a';
	return 0;
}

// Memory
int bar_4_1() {
	int *p[5];
	p[0] = (int *)malloc(sizeof(int) * 5);
	p[0][5] = 'a';
	free(p[0]);
	return 0;
}
