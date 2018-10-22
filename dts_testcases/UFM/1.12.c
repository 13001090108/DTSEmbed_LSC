#include <stdlib.h>
int foo_1_12(char *f, int i) {
	f = (char*)malloc(sizeof(char));
	free(f);
	if (i && *f != 'a') {
		// do something
	}
	return 0;
}
