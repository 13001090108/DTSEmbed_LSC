#include <stdlib.h>
int foo_1_11(char *f) {
	f = (char*)malloc(sizeof(char));
	free(f);
	if (*f) {
		// do something
	}
	return 0;
}
