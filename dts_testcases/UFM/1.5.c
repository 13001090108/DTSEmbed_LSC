#include <stdlib.h>
int foo_1_5(char *f) {
	f = (char*)malloc(sizeof(char));
	free(f);
	if (f) {
		/* do something */
	}
	*f = 'a';
	return 0;
}
