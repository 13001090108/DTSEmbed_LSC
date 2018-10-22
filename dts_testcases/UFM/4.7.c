#include <stdlib.h>
int foo_4_7() {
	char *f[10];
	f[0] = (char*)malloc(sizeof(char));
	free(f[0]);
	*f[0] = 1;
	if (f[0]) {
		/* do something */
	}
	return 0;
}
