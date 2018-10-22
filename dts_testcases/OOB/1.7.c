#include <stdlib.h>

// Array
int foo_1_7() {
	char p[5] = {0};
	p[5] = 'a';
	if (!p[5]) ;
	return 0;
}

// Memory
int bar_1_7() {
	int *p;
	p = (int *)malloc(sizeof(int) * 5);
	p[5] = 'a';
	if (!p) ;
	free(p);
	return 0;
}
