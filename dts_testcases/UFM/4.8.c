#include <stdlib.h>
int foo_4_8(int i) {
	char *f[10];
	f[0] = (char*)malloc(sizeof(char));
	free(f[0]);
	*f[0] = 1;
	if (i || f[0]) {
		/* do something */
	}
	return 0;
}
