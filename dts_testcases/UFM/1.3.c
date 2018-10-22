#include <stdlib.h>
int foo_1_3(int i, char *f) {
	f = (char*)malloc(sizeof(char));
	free(f);
	if (i || f)
		*f = 'a';
	return 0;
}
