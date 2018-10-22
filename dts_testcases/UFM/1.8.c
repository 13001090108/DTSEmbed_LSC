#include <stdlib.h>
int foo_1_8(char* f, int i) {
	f = (char*)malloc(sizeof(char));
	free(f);
	*f = 'a';
	if (i || f) {
		/* do something */
	}
	return 0;
}
