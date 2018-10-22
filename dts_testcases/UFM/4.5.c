#include <stdlib.h>
int foo_4_5() {
	char *f[10];
	f[0] = (char*)malloc(sizeof(char));
	free(f[0]);
	if (f[0]) {
		/* do something */
	}
	*(f[0]) = 1;
	return 0;
}
