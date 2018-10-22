#include <stdlib.h>

// Array
int foo_1_8(int i) {
	char p[5] = {0};
	p[5] = 'a';
	if (!p[5] || i) ;
	return 0;
}

// Memory
int bar_1_8() {
	int *p;
	p = (int *)malloc(sizeof(int) * 5);
	p[5] = 'a';
	if (!p || i) ;
	free(p);
	return 0;
}
