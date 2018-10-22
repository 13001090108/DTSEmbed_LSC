#include <stdlib.h>

// Array
int foo_4_6(int i) {
	char p[5][5] = {0};
	if (!p[0][5] || i) ;
	p[0][5] = 'a';
	return 0;
}

// Memory
int bar_4_6() {
	int *p[5];
	p[0] = (int *)malloc(sizeof(int) * 5);
	if (!p[0] || i) ;
	p[0][5] = 'a';
	free(p[0]);
	return 0;
}
