#include <stdlib.h>
char *foo_5_2() {
	char *p = (char *)malloc(sizeof(char));
	free(p);
	return p;
}
int bar_5_2() {
	if (foo_5_2())
		*foo_5_2() = 'a';
	return 0;
}
