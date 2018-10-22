#include <stdlib.h>
int foo_4_6(int i) {
	char *f[10];
	f[0] = (char*)malloc(sizeof(char));
	free(f[0]);
	if (f[0] || i) {
		/* do something */
	}
	*f[0] = 1;
	return 0;
}
