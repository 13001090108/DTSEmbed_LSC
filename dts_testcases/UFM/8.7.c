#include <stdlib.h>
char *bar_8_7(char *p) {
	free(p);
	return p;
}
void foo_8_7(char p) {
}
int baz_8_7() {
	char *p = (char *)malloc(sizeof(char));
	foo_8_7(*bar_8_7(p));
	return 0;
}
