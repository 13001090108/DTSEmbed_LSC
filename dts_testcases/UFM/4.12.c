#include <stdlib.h>
int foo_4_12(int i) {
	char *p[10] = {0};
	p[0] = (char*)malloc(sizeof(char));
	free(p[0]);
	if (i || *p[0] != 'a') {
		// do something
	}
	return 0;
}
