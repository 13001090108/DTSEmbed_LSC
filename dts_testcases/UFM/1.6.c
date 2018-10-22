#include <stdlib.h>
int foo_1_6(char *f, int i) {
	f = (char*)malloc(sizeof(char));
	free(f);
	if (i || f) {
		/* do something */
	}
	*f = 'a';
	return 0;
}
