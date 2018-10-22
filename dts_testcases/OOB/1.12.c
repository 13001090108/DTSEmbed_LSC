#include <stdlib.h>

// Array
int foo_1_12(int i) {
	char p[5];
	if (p[5] != 'a') ;
	return 0;
}

// Memory
int bar_1_12(int i) {
	int *p;
	p = (int *)malloc(sizeof(int) * 5);
	if (p[5] != 'a') ;
	free(p);
	return 0;
}
