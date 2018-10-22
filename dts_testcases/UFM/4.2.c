#include <stdlib.h>
int foo_4_2() {
	char *f[10];
	f[0] = (char*)malloc(sizeof(char));
	free(f[0]);
	if (f[0])
		*(f[0]) = 'a';
	return 0;
}
