#include <stdlib.h>
char *p[10];
void foo_6_5() {
	*p[0] = 'a';
}
int bar_6_5() {
	p[0] = (char *)malloc(sizeof(char));
	free(p[0]);
	foo_6_5();
	return 0;
}
