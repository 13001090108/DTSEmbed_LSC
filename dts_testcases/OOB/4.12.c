#include <stdlib.h>

// Array
int foo_4_12(int i) {
	char p[5][5];
	if (p[0][5] != 'a') ;
	return 0;
}

// Memory
int bar_4_12(int i) {
	int *p[5];
	p[0] = (int *)malloc(sizeof(int) * 5);
	if (p[0][5] != 'a') ;
	free(p[0]);
	return 0;
}
