#include <stdlib.h>
int foo_1_1(char *f) {
	f = (char*)malloc(sizeof(char));
	free(f);
	*f = 'a';
	return 0;
}
