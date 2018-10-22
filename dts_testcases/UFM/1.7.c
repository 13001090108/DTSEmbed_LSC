#include <stdlib.h>
int foo_1_7(char *f, int i) {
	f = (char*)malloc(sizeof(char));
	free(f);
	*f = 'a';
	if (!f) {
		/* do something */
	}
	return 0;
}
