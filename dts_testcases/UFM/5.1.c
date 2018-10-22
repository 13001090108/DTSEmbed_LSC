#include <stdlib.h>
char *foo_5_1(char *p) {
	free(p);
	return p;
}
int bar_5_1() {
	char *p = (char *)malloc(sizeof(char));
	*foo_5_1(p) = 'a';
	return 0;
}
