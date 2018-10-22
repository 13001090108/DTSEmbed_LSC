#include <stdlib.h>
void foo_7_1(char *p) {
	*p = 'a';
}
void bar_7_1(char *p) {
	foo_7_1(p);
}
int baz_7_1() {
	char *p = (char *)malloc(sizeof(char));
	free(p);
	//foo_7_1(p);
	bar_7_1(p);
	return 0;
}
