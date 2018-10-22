#include <stdlib.h>
int foo_4_11() {
	char *p[10] = {0};
	p[0] = (char*)malloc(sizeof(char));
	free(p[0]);
	if (*p[0] != 'a') {
		// do something
	}
	return 0;
}
