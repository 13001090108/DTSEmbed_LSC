#include <stdlib.h>

// Array
int foo_1_6(int i) {
	char p[5] = {0};
	if (!p[5] || i) ;
	p[5] = 'a';
	return 0;
}

// Memory
int bar_1_6() {
	int *p;
	p = (int *)malloc(sizeof(int) * 5);
	if (!p || i) ;
	p[5] = 'a';
	free(p);
	return 0;
}
