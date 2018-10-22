#include <stdlib.h>

// Array
int foo_4_8(int i) {
	char p[5][5] = {0};
	p[0][5] = 'a';
	if (!p[0][5] || i) ;
	return 0;
}

// Memory
int bar_4_8() {
	int *p[5];
	p[0] = (int *)malloc(sizeof(int) * 5);
	p[0][5] = 'a';
	if (!p[0] || i) ;
	free(p[0]);
	return 0;
}
