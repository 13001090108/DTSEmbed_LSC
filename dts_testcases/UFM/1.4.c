#include <stdlib.h>
int foo_1_4(int i, int j) {
	char *f = (char*)malloc(sizeof(char));
	if (i)
		free(f);
	if(j)
		*f = 1;
	return 0;
}
