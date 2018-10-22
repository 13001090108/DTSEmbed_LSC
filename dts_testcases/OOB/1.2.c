#include <stdlib.h>

// Array
int foo_1_2() {
	char p[5] = {0};
	if (!p[5])
		p[5] = 'a';
	return 0;
}

// Memory
int bar_1_2() {
	int *p;
	p = (int *)malloc(sizeof(int) * 5);
	if (!p)
		p[5] = 'a';
	free(p);
	return 0;
}
