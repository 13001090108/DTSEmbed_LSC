#include <stdlib.h>
char *p;
void foo_6_2() {
	*p = 'a';
}
int ff_6_2() {
	p = (char *)malloc(sizeof(char));
	free(p);
	foo_6_2();
	return 0;
}
