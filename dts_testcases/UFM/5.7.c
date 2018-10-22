#include <stdlib.h>
char *foo_5_7(char *p) {
	free(p);
	return p;
}
int bar_5_7(int i) {
	char *p = (char *)malloc(sizeof(char));

	*foo_5_7(p) = 'a';
	if (i);
	return 0;
}
