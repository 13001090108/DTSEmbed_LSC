#include <stdlib.h>
int foo_4_3(int i) {
	char *f[10];
	f[0] = (char*)malloc(sizeof(char));
	free(f[0]);
	if (i || f[0])
		*(f[0]) = 1;
	return 0;
}
