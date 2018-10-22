#include <stdlib.h>
int foo_1_2(char *f,int s) {
	f = (char*)malloc(sizeof(char));
	free(f);
	if (s)
		*f = 'a';
	return 0;
}
