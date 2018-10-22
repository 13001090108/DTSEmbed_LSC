#include <stdlib.h>
void foo_6_1(char *p) {
	*p = 'a';
}
int ff_6_1() {
	char *p = (char *)malloc(sizeof(char));
	free(p);
	foo_6_1(p);
	return 0;
}
