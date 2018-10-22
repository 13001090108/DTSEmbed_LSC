#include <stdlib.h>

// Array
int foo_4_3(int i) {
	char p[5][5] = {0};
	if (!p[0][5] || i)
		p[0][5] = 'a';
	return 0;
}

// Memory
int bar_4_3(int i) {
	int *p[5];
	p[0] = (int *)malloc(sizeof(int) * 5);
	if (i || !p[0])
		p[0][5] = 'a';
	free(p[0]);
	return 0;
}
