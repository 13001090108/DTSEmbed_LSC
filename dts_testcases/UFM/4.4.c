#include <stdlib.h>
int foo_4_4(int i, int j) {
	char *f[10];
	f[0] = (char*)malloc(sizeof(char));
	if (i)
		free(f[0]);
	if (j)
		*(f[0]) = 'a';
	return 0;
}
